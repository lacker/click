use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

fn entry_cell_after_local_stores(
    store_count: usize,
    overwrite: bool,
    goal: &str,
) -> (String, String) {
    let local_stores = (1..=store_count)
        .map(|value| format!("    i = {value};\n"))
        .collect::<String>();
    let cell_store = if overwrite { "    a[0] = 7;\n" } else { "" };
    let steps = "    step();\n".repeat(store_count + 2 + usize::from(overwrite));
    let c_source = format!(
        "void probe(int32 a[], int32 n) {{\n    int32 i;\n    i = 0;\n{local_stores}{cell_store}}}\n"
    );
    let click_source = format!(
        r#"verifying "probe.c";
void probe(int32 a[], int32 n) {{
    requires 0 < n;
    owns a[0..n];
}} by {{
{steps}    have {goal} by close();
}}
"#
    );
    (c_source, click_source)
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn first_entry_cell_lookup_has_bounded_work_after_disjoint_stores() {
    use crate::instrumentation::{VerificationEvent, collect};

    // The symbolic range gives access to the entry cell without naming its
    // value. The final have is the first proof read of a[0].
    let samples = [4, 16, 64, 256].map(|size| {
        let (c, source) = entry_cell_after_local_stores(size, false, "a[0] == old(a[0])");
        let (verified, events) = collect(|| verify_c_sources(&source, &[("probe.c", &c)]));
        verified.unwrap_or_else(|error| panic!("size {size}: {}", error.message()));

        let start = events
            .iter()
            .position(|event| {
                matches!(event, VerificationEvent::TacticStarted(tactic)
                if tactic.tactic_name == "have")
            })
            .expect("the explicit comparison ran");
        let (end, have_work) = events
            .iter()
            .enumerate()
            .skip(start + 1)
            .find_map(|(index, event)| match event {
                VerificationEvent::TacticFinished { tactic, work, .. }
                    if tactic.tactic_name == "have" =>
                {
                    Some((index, *work))
                }
                _ => None,
            })
            .expect("the explicit comparison finished");
        let walk_work = events[start + 1..end]
            .iter()
            .filter_map(|event| match event {
                VerificationEvent::OperationFinished { name, work, .. }
                    if name == "cell version walk" =>
                {
                    Some(*work)
                }
                _ => None,
            })
            .max()
            .unwrap_or(0);
        (walk_work, have_work)
    });
    let (first_walk, first_have) = samples[0];
    assert!(
        samples
            .iter()
            .all(|&(walk, have)| walk <= first_walk && have <= first_have + 16),
        "cold entry-cell (walk, have) work at 4, 16, 64, and 256 stores: {samples:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4.5s in the parallel gate"]
fn static_cell_read_steps_skip_same_array_store_history() {
    use crate::instrumentation::{VerificationEvent, collect};

    // Each read is the first access to its offset. The fixed store target is
    // in the same array, so the whole-block selector cannot skip the prefix.
    for (local_store, setup, setup_steps, max_read_version_work) in [
        (None, "", 1, 4),
        (Some("x"), "", 1, 4),
        (Some("*p"), "    int32* p;\n    p = &x;\n", 3, 6),
    ] {
        for (stores, reads) in [(4, 1), (16, 1), (64, 1), (128, 1), (32, 32)] {
            let mut c = format!("int32 g[256];\nint32 probe() {{\n    int32 x;\n{setup}");
            let mut prefix_steps = setup_steps;
            for value in 1..=stores {
                c.push_str(&format!("    g[255] = {value};\n"));
                prefix_steps += 1;
                if let Some(lhs) = local_store
                    && value < stores
                {
                    c.push_str(&format!("    {lhs} = {value};\n"));
                    prefix_steps += 1;
                }
            }
            for index in 0..reads - 1 {
                c.push_str(&format!("    x = g[{index}];\n"));
            }
            c.push_str(&format!("    return g[{}];\n}}\n", reads - 1));
            let steps = "    step();\n".repeat(prefix_steps + reads);
            let source = format!(
                r#"verifying "probe.c";
int32 probe() {{
    owns g[0..256];
}} by {{
{steps}}}
"#
            );
            let (verified, events) = collect(|| verify_c_sources(&source, &[("probe.c", &c)]));
            verified.unwrap_or_else(|error| {
                panic!(
                    "local={local_store:?}, stores={stores}, reads={reads}: {}",
                    error.message()
                )
            });
            let mut checking_read = false;
            let mut completed = 0;
            let mut version_work = 0;
            for event in events {
                match event {
                    VerificationEvent::TacticStarted(tactic) if tactic.tactic_name == "step" => {
                        checking_read = tactic.tactic_index >= prefix_steps;
                    }
                    VerificationEvent::TacticFinished { tactic, .. }
                        if tactic.tactic_name == "step" =>
                    {
                        completed += usize::from(checking_read);
                        checking_read = false;
                    }
                    VerificationEvent::OperationFinished { name, work, .. }
                        if checking_read && name == "cell version walk" =>
                    {
                        version_work += work;
                    }
                    _ => {}
                }
            }
            assert_eq!(completed, reads);
            // A direct read after the array stores can use the recorded
            // point's byte index without starting the legacy walk.
            let limit = if local_store.is_none() && reads == 1 {
                0
            } else {
                max_read_version_work * reads
            };
            assert!(
                version_work <= limit,
                "local={local_store:?}, {stores} stores and {reads} reads used {version_work} version work, limit {limit}"
            );
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3.9s in the parallel gate"]
fn static_cell_read_steps_skip_same_array_call_history() {
    use crate::instrumentation::{VerificationEvent, collect};

    for (calls, reads) in [(4, 1), (16, 1), (64, 1), (128, 1), (32, 32)] {
        let mut c = "int32 g[256];\nvoid touch() { g[255] = 1; }\nint32 probe() {\n    int32 x;\n"
            .to_string();
        c.push_str(&"    touch();\n".repeat(calls));
        for offset in 0..reads {
            c.push_str(&format!("    x = g[{offset}];\n"));
        }
        c.push_str("    return 0;\n}\n");
        let steps = "    step();\n".repeat(calls + reads + 2);
        let source = format!(
            r#"verifying "probe.c";
void touch() {{ owns g[255..256]; }}
int32 probe() {{ owns g[0..256]; ensures result == 0; }} by {{
{steps}}}
"#
        );
        let (verified, events) = collect(|| verify_c_sources(&source, &[("probe.c", &c)]));
        verified
            .unwrap_or_else(|error| panic!("{calls} calls, {reads} reads: {}", error.message()));

        let mut steps = 0;
        let mut walk_work = 0;
        let mut load_work = Vec::new();
        for event in events {
            match event {
                VerificationEvent::TacticStarted(tactic)
                    if tactic.claim == "probe.contract" && tactic.tactic_name == "step" =>
                {
                    steps = tactic.tactic_index;
                }
                VerificationEvent::TacticFinished { tactic, work, .. }
                    if tactic.claim == "probe.contract"
                        && tactic.tactic_name == "step"
                        && (calls + 1..=calls + reads).contains(&steps) =>
                {
                    load_work.push(work);
                }
                VerificationEvent::OperationFinished { name, work, .. }
                    if name == "cell version walk"
                        && (calls + 1..=calls + reads).contains(&steps) =>
                {
                    walk_work += work;
                }
                _ => {}
            }
        }
        assert_eq!(load_work.len(), reads);
        assert!(
            walk_work <= 40 * reads && load_work.iter().all(|&work| work <= 240),
            "{calls} calls, {reads} reads: version work {walk_work}, step work {load_work:?}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn writing_the_entry_cell_changes_its_ordinary_read_version() {
    let (c, source) = entry_cell_after_local_stores(4, true, "a[0] == 7");
    verify_c_sources(&source, &[("probe.c", &c)]).expect("the read names the written value");

    let (_, source) = entry_cell_after_local_stores(4, true, "a[0] == old(a[0])");
    let error = verify_c_sources(&source, &[("probe.c", &c)])
        .expect_err("known must not identify the written cell with the entry read");
    assert!(
        error
            .message()
            .contains("`known` requires the current goal as an available semantic fact"),
        "{}",
        error.message()
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn trivial_disjuncts_do_not_spell_unrelated_premises() {
    let mut samples = Vec::new();
    for size in [1, 2, 8] {
        let parameters = (0..size)
            .map(|i| format!(", unused{i}: uint64"))
            .collect::<String>();
        let premises = (0..size)
            .map(|i| format!("requires unused{i} > n;\n"))
            .collect::<String>();
        let source = format!(
            "theorem trivial(n: uint64{parameters}) {{ {premises} ensures true or n == 1u64 by close(); }}"
        );
        let (result, sample) = scaling_sample(size, || verify_c_sources(&source, &[]));
        result.expect("the true disjunct closes without exploring the other side");
        assert_eq!(
            sample
                .named_work
                .get("operation `solve closure: premise raising`")
                .copied()
                .unwrap_or(0),
            0,
            "{sample:?}"
        );
        assert_eq!(
            sample
                .named_work
                .get("operation `atomic dependency selection`")
                .copied()
                .unwrap_or(0),
            0,
            "a direct disjunct must not select connected facts: {sample:?}"
        );
        samples.push(sample);
    }
    assert_near_linear_scaling_at_sampled_sizes(
        "trivial disjunct with unrelated premises",
        &samples,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: constructor closure at three heap-history sizes and cold replay"]
fn refuted_constructor_guards_do_not_spell_connected_heap_history() {
    // The complete pop/deallocate/refold path remains in
    // mdtests/refuted_implication_after_stack_pop.md. Isolate the closure here:
    // its constructor payload names the same cell whose store history grows.
    let guard = "old(before.items) == List<int32>::Nil implies result == 0";
    let mut samples = Vec::new();
    for size in [0, 8, 32] {
        let stores = (0..size).map(|i| format!("*p = {i}; ")).collect::<String>();
        let c = format!("int probe(int *p) {{ {stores}return 1; }}");
        let steps = "step(); ".repeat(size + 1);
        let source = format!(
            r#"
verifying "probe.c";
resource cell(p: int32*) {{
    field items: List<int32>;
    owns p[0..1];
    fact items == List<int32>::Cons(p[0], List<int32>::Nil);
}}
int32 probe(int32* p) {{
    consumes before: cell(p);
    produces after: cell(p);
    ensures result == 1;
}} by {{
    unfold(before);
    {steps}
    have {guard} by close();
    let after = fold(cell(p), {{ items: List<int32>::Cons(p[0], List<int32>::Nil) }}) by {{ close(); }}
    close();
    close();
}}
"#
        );
        let sources = [("probe.c", c.as_str())];
        eprintln!("constructor guard: {size} stores");
        let ((verified, tactics), sample) = scaling_sample(size, || {
            crate::instrumentation::collect_tactic_work(|| verify_c_sources(&source, &sources))
        });
        verified.unwrap_or_else(|error| panic!("{size} stores: {}", error.message()));
        let guards = tactics
            .iter()
            .filter(|t| t.tactic.tactic_name == "have")
            .collect::<Vec<_>>();
        assert_eq!(
            guards.len(),
            1,
            "exactly one constructor guard is measured: {tactics:?}"
        );
        assert!(!guards[0].failed);
        let spelling = sample
            .named_work
            .get("operation `solve closure: premise raising`")
            .copied()
            .unwrap_or(0);
        samples.push((size, guards[0].work, spelling));
        if size == 8 {
            let offset = source.find("close();").unwrap();
            let position = super::super::expansion::position_at_offset(&source, offset);
            let expanded =
                expand_c_tactic_source_at(&source, &sources, position.line, position.column)
                    .expect("the selected constructor guard expands");
            assert!(!expanded.contains("solve();"), "{expanded}");
            crate::surface::without_implicit_solve_for_claim("probe.contract", || {
                verify_c_sources(&expanded, &sources).map_err(|error| error.message().to_owned())
            })
            .expect("the explicit guard refutation cold-replays");
            // The opposite guard holds for this nonempty constructor, while
            // the returned value is 1. Reject it with and without the certificate.
            for (proof, explicit) in [(&source, false), (&expanded, true)] {
                let invalid = proof.replace(
                    "old(before.items) == List<int32>::Nil",
                    "old(before.items) != List<int32>::Nil",
                );
                assert_ne!(&invalid, proof);
                let verify = || {
                    verify_c_sources(&invalid, &sources).map_err(|error| error.message().to_owned())
                };
                let result = if explicit {
                    crate::surface::without_implicit_solve_for_claim("probe.contract", verify)
                } else {
                    verify()
                };
                let error = result.unwrap_err();
                assert!(!error.contains("budget"), "{error}");
            }
        }
    }
    eprintln!("constructor guard (stores, closure work, premise raising): {samples:?}");
    assert!(
        samples.iter().all(|(_, _, spelling)| *spelling == 0),
        "{samples:?}"
    );
    // `have` accounting includes opening and checking the goal, not just
    // search. Bound its growth separately from the zero-spelling assertion:
    // the second interval adds three times as many stores, so allow at most
    // four times the added work. Subtract setup so it cannot hide curvature.
    let first_increment = samples[1].1.saturating_sub(samples[0].1);
    let next_increment = samples[2].1.saturating_sub(samples[1].1);
    assert!(next_increment <= 4 * first_increment, "{samples:?}");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn refined_pure_arithmetic_does_not_rescan_unrelated_parameters() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/pure_arithmetic_retains_a_rewritten_fold_goal.md");
    let fixture = crate::cli::parse_mdtest(
        &path,
        include_str!("../../../../mdtests/pure_arithmetic_retains_a_rewritten_fold_goal.md"),
    )
    .unwrap();
    let source = fixture.click_source.unwrap();
    let definitions = source.split_once("theorem count_step").unwrap().0;
    let mut samples = Vec::new();
    for size in [0, 4, 16, 64] {
        let parameters = (0..size)
            .map(|index| format!(", unused{index}: uint64"))
            .collect::<String>();
        let source = format!(
            "{definitions}
theorem count_step(n: uint64{parameters}) {{
    requires to_integer(0u64) <= to_integer(n - 1u64);
    requires to_integer(n - 1u64) < to_integer(18446744073709551615u64);
    requires full_width_count(n - 1u64) == to_integer(n - 1u64);
    requires to_integer(n - 1u64) == to_integer(n) - to_integer(1u64);
    ensures full_width_count(n) == to_integer(n) by {{
        unfold(full_width_count(n));
        rewrite(full_width_count(n - 1u64), to_integer(n - 1u64));
        rewrite(to_integer(n - 1u64), to_integer(n) - to_integer(1u64));
        close() using {{}};
    }}
}}"
        );
        let (result, work) =
            crate::instrumentation::collect_tactic_work(|| verify_click_theorems(&source));
        result.unwrap();
        let work = work
            .iter()
            .rfind(|sample| sample.tactic.tactic_name == "close")
            .expect("the final arithmetic closure ran")
            .work;
        samples.push((size, work));
    }
    let baseline = samples[0].1;
    assert!(
        samples.iter().all(|(_, work)| *work <= baseline + 32),
        "unrelated parameters grew the refined arithmetic step: {samples:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: multi-size quantified frame refusal and positive controls"]
fn false_quantified_frames_do_not_materialize_the_constant_domain() {
    use crate::instrumentation::measure_deterministic_work;
    verify_c_sources("theorem warm() { ensures true by close(); }", &[]).unwrap();
    let program = "int32 untouched_element(int32* a) { unsigned char* b; b = (unsigned char*)(void*) a; b[5] = 7; return a[2]; }";
    let mut samples = Vec::new();
    for size in [16, 1024, 1_000_000, 100_000_000] {
        let mut pair = Vec::new();
        for false_frame in [false, true] {
            let frame = if false_frame {
                format!("ensures (0..{size}).all(|k| {{ a[k] == old(a[k]) }});")
            } else {
                String::new()
            };
            let source = format!(
                "verifying \"probe.c\"; int32 untouched_element(int32* a) {{ owns a[0..{size}]; ensures result == old(a[2]); {frame} }}"
            );
            let (result, work) =
                measure_deterministic_work(|| verify_c_sources(&source, &[("probe.c", program)]));
            if false_frame {
                let error = result.expect_err("the byte store invalidates the whole-range frame");
                assert!(error.message().contains(".all"), "{}", error.message());
                assert!(
                    !error.message().contains("budget exhausted"),
                    "{}",
                    error.message()
                );
            } else {
                result.expect("the untouched element retains its entry value");
            }
            pair.push(work);
        }
        samples.push((size, pair));
    }
    for sample in &samples {
        assert!(
            sample.1[1] <= samples[0].1[1] * 2,
            "domain-dependent refusal: {samples:?}"
        );
    }
    eprintln!("quantified frame work (size, [true, false]): {samples:?}");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: multi-size reference-call refusal and positive controls"]
fn refusing_a_false_literal_result_after_calls_scales_with_the_true_result() {
    use crate::instrumentation::{VerificationEvent, collect, measure_deterministic_work};
    verify_c_sources("theorem warm() { ensures true by close(); }", &[]).unwrap();
    let mut samples = Vec::new();
    for size in [4, 8, 16, 32] {
        let parameters = (0..size)
            .map(|i| format!("int32 unused{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let locals = (0..size)
            .map(|i| format!("int32 local{i} = {i};"))
            .collect::<Vec<_>>()
            .join("\n");
        let calls = "read(p);\n".repeat(size);
        let program = format!(
            "int32 read(int32* p) {{ return p[0]; }}\nint32 many({parameters}, int32* p) {{ {locals} {calls} return p[0]; }}"
        );
        let mut pair = Vec::new();
        for value in [7, 8] {
            let source = format!(
                r#"
                verifying "calls.c";
                int32 read(int32* p) {{ owns p[0..1]; ensures result == old(p[0]); ensures p[0] == old(p[0]); }}
                int32 many({parameters}, int32* p) {{ owns p[0..1]; requires p[0] == 7; ensures result == {value}; ensures p[0] == 7; }} by {{
                    step_until(function.exit);
                    have result == 7 by close();
                    have result == {value} by close() using {{ result == 7; }};
                    close();
                }}
            "#
            );
            let ((result, events), total) = measure_deterministic_work(|| {
                collect(|| verify_c_sources(&source, &[("calls.c", program.as_str())]))
            });
            if value == 7 {
                result.expect("the unchanged reference value should verify");
            } else {
                let error = result.expect_err("the false result must be refused");
                assert!(
                    !error.message().contains("budget exhausted"),
                    "{}",
                    error.message()
                );
            }
            let work: usize = events
                .iter()
                .filter_map(|event| match event {
                    VerificationEvent::OperationFinished {
                        function,
                        name,
                        work,
                        ..
                    } if function == "many" && name == "post-execution claim tactics" => {
                        Some(*work)
                    }
                    _ => None,
                })
                .sum();
            assert!(work > 0, "missing finishing-work observation");
            pair.push((total, work));
        }
        assert!(
            pair[1].0 <= pair[0].0 * 2,
            "N={size}: false {} versus true {}",
            pair[1].0,
            pair[0].0
        );
        samples.push((size, pair[0], pair[1]));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].2.1 <= pair[0].2.1 * 3,
            "superlinear refusal: {samples:?}"
        );
    }
    eprintln!(
        "reference-call work (size, (true total, finishing), (false total, finishing)): {samples:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.8s in the parallel gate"]
fn expanded_loop_claims_preserve_the_audit_work_bound() {
    for (fixture, claim) in [
        ("c_decreases_recursive_in_loop", "recursive_loop.contract"),
        ("later_loop_preserve", "later_loop_preserve.contract"),
        ("loop_exit_program_point", "count_from_to.contract"),
        ("nested_loop_preserve", "nested_loop_preserve.contract"),
    ] {
        let path =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("mdtests/{fixture}.md"));
        let markdown = std::fs::read_to_string(&path).unwrap();
        let input = crate::cli::parse_mdtest(&path, &markdown).unwrap();
        let source = input.click_source.as_deref().unwrap();
        let sources = input
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let expanded =
            crate::surface::expand_c_claim_source_by_label(source, &sources, claim).unwrap();
        let samples = [source, expanded.as_str()].map(|source| {
            let position =
                crate::surface::c_tactic_source_position(source, &sources, claim, 0).unwrap();
            let (result, sample) = scaling_sample(0, || {
                crate::surface::verify_c_sources_at(
                    source,
                    &sources,
                    position.line,
                    position.column,
                )
            });
            result.unwrap();
            sample
        });
        assert!(
            samples[1].work <= samples[0].work * 2 || samples[1].work <= samples[0].work + 10_000,
            "{fixture}: original {}, expanded {}; {}",
            samples[0].work,
            samples[1].work,
            named_growth_diagnostic(&samples)
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn execution_target_resource_scope_parsing_is_linear_in_selected_declarations() {
    let samples = [1, 8, 32, 128].map(|count| {
        let mut source = "resource Counter() { field revision: int32; }\n".to_string();
        for index in 0..count {
            source.push_str(&format!("theorem lift{index}(callback: int32 (*)()) executes callback() {{ requires C{index}(callback); ensures C{index}(callback) as {{ cell: k }} by {{ step(C{index}, {{ cell: k }}); close(); }} }}\n"));
        }
        for index in 0..count {
            source.push_str(&format!("contract int32 C{index}() {{ owns cell: Counter(); ensures result == 0; }}\n"));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::surface::parse(&source).expect("forward target proof scopes parse")
        });
        (count, work)
    });
    assert!(samples[0].1 > 0);
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * (pair[1].0 / pair[0].0),
            "{samples:?}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn reversed_all_arm_matching_scales_with_written_labels() {
    fn conjunction(labels: &[String]) -> String {
        if let [one] = labels {
            return one.clone();
        }
        let (left, right) = labels.split_at(labels.len() / 2);
        format!("({} and {})", conjunction(left), conjunction(right))
    }

    let mut samples = Vec::new();
    for width in [4, 8, 16, 32] {
        let goals = (0..width)
            .map(|index| format!("(forall (i: int32) {{ i <= i or i == {index} }})"))
            .collect::<Vec<_>>();
        let arms = (0..width)
            .rev()
            .map(|index| {
                format!(
                    "forall (j: int32) {{ j <= j or j == {index} }} => {{ intro() {{ close(); }} }}"
                )
            })
            .collect::<Vec<_>>()
            .join("\n");
        let source = format!(
            "theorem reordered() {{ ensures {} by {{ all {{ {arms} }} }} }}",
            conjunction(&goals)
        );
        let (result, sample) = scaling_sample(width, || verify_click_theorems(&source));
        result.expect("reversed and alpha-renamed arms match their goals");
        samples.push(sample);
    }
    assert_near_linear_scaling("reversed conjunction arm matching", &samples);
}

#[test]
fn nested_conjunction_body_parsing_uses_small_frames_and_linear_work() {
    // `surface::parse` expands a file against the standard library, whose
    // first use parses every library module into a process-wide `OnceLock`
    // on the calling thread. Do that here, on the test's ordinary stack, so
    // the small stack and the work samples measure only the nested bodies.
    crate::surface::parse("theorem warm() { ensures 0 == 0 by { close(); } }")
        .expect("the standard library parses");
    std::thread::Builder::new()
        .name("small-stack-proof-body-parser".into())
        .stack_size(7 * 256 * 1024)
        .spawn(|| {
            let samples = [2, 4, 8, 16].map(|depth| {
                let mut body = "have 0 == 0 by { close(); } close();".to_string();
                for _ in 0..depth {
                    body = format!("all {{ true => {{ {body} }} true => {{ close(); }} }}");
                }
                let source = format!("theorem nested() {{ ensures 0 == 0 by {{ {body} }} }}");
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    crate::surface::parse(&source)
                        .expect("nested proof bodies should parse on the ordinary stack")
                });
                work
            });
            for pair in samples.windows(2) {
                assert!(
                    pair[1] <= pair[0].saturating_mul(2).saturating_add(8),
                    "{samples:?}"
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn repeated_execution_matches_keep_terminal_case_evidence_and_scale_linearly() {
    // Repeated matches can produce coincident outcome/fact records with
    // distinct case evidence. Every checked leaf must survive publication.
    std::thread::Builder::new()
        .name("repeated-execution-match-evidence".into())
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            // Initialize shared library definitions before measuring the
            // selected proof, consistently with the other scaling fixtures.
            verify_c_sources("theorem warm() { ensures true by close(); }", &[]).unwrap();
            let c = [("unit.c", "int32 unit(void) { return 0; }")];
            let mut samples = Vec::new();
            for depth in [1, 2, 4, 8] {
                let mut body = "step(); close();".to_string();
                for _ in 0..depth {
                    body = format!("match m.model {{ Kind::A => {{ {body} }}, Kind::B => {{ step(); close(); }}, }}");
                }
                let source = format!(
                    "verifying \"unit.c\";
spec enum Kind {{ A, B }}
resource marker() {{ field model: Kind; fact true; }}
int32 unit() {{ owns m: marker(); ensures result == 0; }} by {{ {body} }}"
                );
                let (verified, sample) = scaling_sample(depth, || verify_c_sources(&source, &c));
                let verified = verified.expect("nested constructor arms verify on the CLI stack");
                samples.push(sample);
                if depth == 8 {
                    let expanded =
                        expand_checked_function_claim(&source, &verified, "unit.contract")
                            .expect("the nested claim expands");
                    without_implicit_solve(|| verify_c_sources(&expanded, &c))
                        .expect("the nested expansion verifies independently");
                    let invalid = source.replace("ensures result == 0", "ensures result == 1");
                    assert!(verify_c_sources(&invalid, &c).is_err());
                }
            }
            assert_near_linear_scaling_with_increment_bound("repeated execution match case evidence", &samples);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn nested_execution_matches_fit_the_cli_stack_and_scale_linearly() {
    // The CLI's ordinary eight-megabyte stack must suffice: the fixture
    // harness's larger stack would hide the captured split-record frames.
    std::thread::Builder::new()
        .name("nested-execution-match-stack".into())
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            // Initialize shared library definitions before measuring the
            // selected proof, consistently with the other scaling fixtures.
            verify_c_sources("theorem warm() { ensures true by close(); }", &[]).unwrap();
            let c = [("unit.c", "int32 unit(void) { return 0; }")];
            let mut samples = Vec::new();
            for depth in [1, 2, 4, 8, 10] {
                let mut body = "step(); close();".to_string();
                for _ in 0..depth {
                    body = format!("match m.model {{ Unit::Only => {{ {body} }}, }}");
                }
                let source = format!(
                    "verifying \"unit.c\";
spec enum Unit {{ Only }}
resource marker() {{ field model: Unit; fact true; }}
int32 unit() {{ owns m: marker(); ensures result == 0; }} by {{ {body} }}"
                );
                let (verified, sample) = scaling_sample(depth, || verify_c_sources(&source, &c));
                let verified = verified.expect("nested constructor arms verify on the CLI stack");
                if depth <= 8 {
                    samples.push(sample);
                }
                if depth == 10 {
                    let expanded =
                        expand_checked_function_claim(&source, &verified, "unit.contract")
                            .expect("the nested claim expands");
                    without_implicit_solve(|| verify_c_sources(&expanded, &c))
                        .expect("the nested expansion verifies independently");
                    let invalid = source.replace("ensures result == 0", "ensures result == 1");
                    assert!(verify_c_sources(&invalid, &c).is_err());
                }
            }
            assert_near_linear_scaling_with_increment_bound("nested execution matches", &samples);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn explicit_constructor_unfold_has_near_linear_nested_match_work() {
    let mut samples = Vec::new();
    for size in [2, 4, 8, 16, 32, 64] {
        let mut body = "n".to_string();
        for index in 0..size {
            body = format!(
                "match Nat::Zero {{ Nat::Zero => {body}, Nat::Succ(unused_{index}) => n, }}"
            );
        }
        let source = format!(
            "function nested(n: Nat) -> Nat {{ {body} }}\n\
            theorem nested_result(n: Nat) {{ ensures nested(n) == n by {{ unfold(nested(n)); close(); }} }}"
        );
        if size > parser::MATCH_NESTING_LIMIT {
            let error = verify_click_theorems(&source)
                .expect_err("deep syntax must fail locally, not overflow the stack");
            assert!(
                error
                    .message()
                    .contains("match nesting exceeds Click's supported depth of 16"),
                "{error:?}"
            );
            continue;
        }
        let (result, sample) = scaling_sample(size, || verify_click_theorems(&source));
        result.expect("explicit constructor matches unfold and check");
        samples.push(sample);
    }
    assert_near_linear_scaling("nested constructor unfolding", &samples);
}

#[test]
fn symbolic_integer_match_lowering_has_near_linear_width_work() {
    let mut samples = Vec::new();
    for width in [8, 16, 32, 64] {
        let variants = (0..width)
            .map(|index| format!("V{index}(Integer)"))
            .collect::<Vec<_>>()
            .join(", ");
        let arms = (0..width)
            .map(|index| {
                format!(
                    "Choice::V{index}(value_{index}) => match Box::Wrapped(value_{index}) {{ Box::Empty => 0, Box::Wrapped(inner_{index}) => inner_{index}, }}"
                )
            })
            .collect::<Vec<_>>()
            .join(",\n                ");
        let source = format!(
            "spec enum Box {{ Empty, Wrapped(Integer) }}\n\
             spec enum Choice {{ {variants} }}\n\
             theorem nested(value: Integer) {{\n\
                 ensures match Choice::V0(value) {{\n\
                     {arms}\n\
                 }} == value by {{ close(); }}\n\
             }}"
        );
        let (result, sample) = scaling_sample(width, || verify_click_theorems(&source));
        result.unwrap_or_else(|error| {
            panic!(
                "width {width} symbolic Integer match failed: {}",
                error.message()
            )
        });
        samples.push(sample);
    }
    assert_near_linear_scaling("symbolic Integer match lowering", &samples);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn symbolic_integer_match_lowering_has_near_linear_nested_depth_work() {
    let mut samples = Vec::new();
    for depth in [2, 4, 8, 16, 32, 64] {
        let mut body = "0".to_string();
        for index in 0..depth {
            body = format!(
                "match Box::Empty {{ Box::Empty => {body}, Box::Wrapped(inner_{index}) => inner_{index}, }}"
            );
        }
        let source = format!(
            "spec enum Box {{ Empty, Wrapped(Integer) }}\n\
             theorem nested() {{ ensures {body} == 0 by {{ close(); }} }}"
        );
        if depth > parser::MATCH_NESTING_LIMIT {
            let error = verify_click_theorems(&source)
                .expect_err("deep Integer matches must fail at the parser boundary");
            assert!(
                error
                    .message()
                    .contains("match nesting exceeds Click's supported depth of 16"),
                "{error:?}"
            );
            continue;
        }
        let (result, sample) = scaling_sample(depth, || verify_click_theorems(&source));
        result.unwrap_or_else(|error| {
            panic!(
                "depth {depth} symbolic Integer match failed: {}",
                error.message()
            )
        });
        samples.push(sample);
    }
    assert_near_linear_scaling("symbolic Integer nested-match lowering", &samples);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn parametric_theorem_declarations_have_near_linear_checking_work() {
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let source = (0..size)
            .map(|index| {
                format!(
                    "theorem reflexive_{index}<T>(x: T) {{ ensures x == x by {{ close(); }} }}\n"
                )
            })
            .collect::<String>();
        let (verified, sample) = scaling_sample(size, || verify_click_theorems(&source));
        assert_eq!(
            verified.expect("every unused generic proof checks").len(),
            size
        );
        samples.push(sample);
    }
    assert_near_linear_scaling("parametric declarations", &samples);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn transitive_module_chains_prepare_with_near_linear_deterministic_work() {
    let mut samples = Vec::new();
    for size in [4, 8, 16, 32] {
        let mut modules = Vec::new();
        modules.push(ClickModuleSource::new(
            "module_0.click",
            "function value_0(x: int32) -> int32 { x }",
            [],
        ));
        for index in 1..size {
            modules.push(ClickModuleSource::new(
                format!("module_{index}.click"),
                format!(
                    "import \"module_{}.click\"; function value_{index}(x: int32) -> int32 {{ value_{}(x) }}",
                    index - 1,
                    index - 1
                ),
                [format!("module_{}.click", index - 1)],
            ));
        }
        modules.push(ClickModuleSource::new(
            "entry.click",
            format!("import \"module_{}.click\";", size - 1),
            [format!("module_{}.click", size - 1)],
        ));
        let project = ClickProject::new("entry.click", modules);
        let (resolved, sample) = scaling_sample(size, || resolve_click_project(&project, &[]));
        assert_eq!(
            resolved
                .expect("the module chain should resolve")
                .click_function_definitions()
                .len(),
            size
        );
        samples.push(sample);
    }
    assert_near_linear_scaling("transitive Click module chains", &samples);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn module_diamonds_prepare_shared_interfaces_once_per_selected_graph() {
    let mut samples = Vec::new();
    for width in [4, 8, 16, 32] {
        let mut modules = vec![ClickModuleSource::new(
            "shared.click",
            "spec enum SharedValue { Value(int32), }",
            [],
        )];
        let mut entry_imports = Vec::new();
        let mut entry_source = String::new();
        for index in 0..width {
            let identity = format!("branch_{index}.click");
            entry_source.push_str(&format!("import \"{identity}\";\n"));
            entry_imports.push(identity.clone());
            modules.push(ClickModuleSource::new(
                identity,
                format!(
                    "import \"shared.click\"; function branch_{index}(x: SharedValue) -> SharedValue {{ x }}"
                ),
                ["shared.click".to_string()],
            ));
        }
        modules.push(ClickModuleSource::new(
            "entry.click",
            entry_source,
            entry_imports,
        ));
        let project = ClickProject::new("entry.click", modules);
        let (resolved, sample) = scaling_sample(width, || resolve_click_project(&project, &[]));
        let resolved = resolved.expect("the module diamond should resolve");
        assert_eq!(resolved.algebraic_type_definitions().len(), 1);
        assert_eq!(resolved.click_function_definitions().len(), width);
        samples.push(sample);
    }
    assert_near_linear_scaling("Click module diamonds", &samples);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn shared_imported_proof_bodies_stay_unselected_across_entry_scaling() {
    let mut samples = Vec::new();
    for entries in [2, 4, 8, 16] {
        let (results, sample) = scaling_sample(entries, || {
            super::super::proof::PROVED_THEOREMS.with(|proved| proved.borrow_mut().clear());
            for index in 0..entries {
                let project = ClickProject::new(
                    format!("entry_{index}.click"),
                    [
                        ClickModuleSource::new(
                            "shared.click",
                            "theorem shared_false(x: int32) { ensures x == x + 1 by close(); }",
                            [],
                        ),
                        ClickModuleSource::new(
                            format!("entry_{index}.click"),
                            format!(
                                "import \"shared.click\"; theorem local_{index}(x: int32) {{ ensures x == x + 1 by {{ apply(shared_false(x)); close(); }} }}"
                            ),
                            ["shared.click".to_string()],
                        ),
                    ],
                );
                verify_c_project(&project, &[])?;
            }
            Ok::<_, ClickError>(())
        });
        results.expect("every selected entry should assume the shared theorem statement");
        super::super::proof::PROVED_THEOREMS.with(|proved| {
            let proved = proved.borrow();
            assert_eq!(proved.len(), entries);
            assert!(proved.iter().all(|name| name.starts_with("local_")));
        });
        samples.push(sample);
    }
    assert_near_linear_scaling("shared imported theorem across selected entries", &samples);
}

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

// Retain the original largest doubling and its 3x work limit while
// skipping a smaller intermediate fixture. Normalize the other interval by
// its actual source-size ratio with the same 3/2 allowance per input unit.
fn near_linear_scaling_at_sampled_sizes(samples: &[ScalingSample]) -> bool {
    samples.len() >= 3
        && samples
            .iter()
            .all(|sample| sample.size > 0 && sample.work > 0)
        && samples.windows(2).all(|pair| {
            pair[0].size < pair[1].size
                && (pair[1].work as u128) * (pair[0].size as u128) * 2
                    <= (pair[0].work as u128) * (pair[1].size as u128) * 3
        })
}

fn assert_near_linear_scaling_at_sampled_sizes(axis: &str, samples: &[ScalingSample]) {
    assert!(
        near_linear_scaling_at_sampled_sizes(samples),
        "{axis}: deterministic work grows faster than the sampled source: {samples:?}; named work: {}",
        named_growth_diagnostic(samples)
    );
}

fn assert_near_linear_scaling(axis: &str, samples: &[ScalingSample]) {
    assert!(
        near_linear_scaling(samples),
        "{axis}: deterministic work grows faster than the simple-verification contract: {samples:?}; named work: {}",
        named_growth_diagnostic(samples),
    );
}

/// Bound curvature separately from fixed setup. On geometric endpoints
/// M/4, M/2, M, a 20/7 increment ratio bounds the quadratic coefficient in
/// B + k*N + a*N^2 by a <= k/M. The old 3x whole-work check at M and 2M
/// allowed a <= k/M + 2*B/M^2, so setup cannot hide that crossover here.
fn assert_bounded_work_increments(
    axis: &str,
    work: &[usize],
    numerator: usize,
    denominator: usize,
) {
    assert!(work.len() >= 3);
    let tail = &work[work.len() - 3..];
    let earlier = tail[1].checked_sub(tail[0]);
    let later = tail[2].checked_sub(tail[1]);
    assert!(
        matches!((earlier, later), (Some(earlier), Some(later)) if later * denominator <= earlier * numerator),
        "{axis}: work increments grew too quickly: {work:?}"
    );
}

fn assert_near_linear_scaling_with_increment_bound(axis: &str, samples: &[ScalingSample]) {
    assert_near_linear_scaling(axis, samples);
    assert_bounded_work_increments(
        axis,
        &samples.iter().map(|sample| sample.work).collect::<Vec<_>>(),
        20,
        7,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn bounded_statement_successor_exclusion_ignores_unrelated_ambient_facts() {
    let (replace_source, caller_source, base_click) =
        super::contract_tests::result_case_split_sources();
    let insertion = "                with(allocated_cell(owner)) {\n                }\n";
    let mut samples = Vec::new();
    let mut exclusion_work = Vec::new();
    for size in [2, 4, 8, 16] {
        let unrelated = (0..size)
            .map(|index| {
                format!(
                    "                have 0 <= {index} by {{\n                    close() using {{}};\n                }}\n"
                )
            })
            .collect::<String>();
        let click_source = base_click.replacen(insertion, &format!("{insertion}{unrelated}"), 1);
        assert_ne!(
            click_source, base_click,
            "the ambient facts were not inserted"
        );
        let (verified, sample) = scaling_sample(size, || {
            verify_c_sources(
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
    // 28/11 at 4/8/16 has the former 20/7-at-8/16/32
    // quadratic crossover, with the same constant selected-operation check.
    assert_bounded_work_increments(
        "bounded statement-successor ambient facts",
        &samples.iter().map(|sample| sample.work).collect::<Vec<_>>(),
        28,
        11,
    );
}

/// Lowering a specification `if` folds a literally constant condition and
/// otherwise lowers both branches. It reads no ambient fact, so checking a
/// requirement that contains one must cost the same whatever else the caller
/// happens to know. The requirement here is a conditional the caller cannot
/// settle, which is the case a branch-deciding lowering would have searched
/// for.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn specification_conditional_lowering_ignores_unrelated_ambient_facts() {
    let mut samples = Vec::new();
    let mut requirement_work = Vec::new();
    for size in [8, 16, 32, 64] {
        let unrelated = (0..size)
            .map(|index| format!("    have 0 <= {index} by {{\n        close();\n    }}\n"))
            .collect::<String>();
        let click_source = format!(
            "verifying \"conditional_callee.c\";\n\
             verifying \"conditional_caller.c\";\n\
             \n\
             int32 conditional_callee(int32 flag, int32 left, int32 right) {{\n    \
                 requires (if flag != 0 {{ left }} else {{ right }}) == 7;\n    \
                 ensures result == 0;\n\
             }}\n\
             \n\
             int32 conditional_caller(int32 flag, int32 left, int32 right) {{\n    \
                 requires (if flag != 0 {{ left }} else {{ right }}) == 7;\n    \
                 ensures result == 0;\n\
             }} by {{\n{unrelated}    step_until(function.exit);\n    close();\n}}\n"
        );
        let (verified, sample) = scaling_sample(size, || {
            verify_c_sources(
                &click_source,
                &[
                    (
                        "conditional_callee.c",
                        "int32 conditional_callee(int32 flag, int32 left, int32 right) {\n    return 0;\n}\n",
                    ),
                    (
                        "conditional_caller.c",
                        "int32 conditional_caller(int32 flag, int32 left, int32 right) {\n    return conditional_callee(flag, left, right);\n}\n",
                    ),
                ],
            )
        });
        verified.expect("a conditional requirement should check under unrelated ambient facts");
        requirement_work.push(
            sample
                .named_work
                .get("operation `verified call requirement checking`")
                .copied()
                .unwrap_or(0),
        );
        samples.push(sample);
    }
    assert!(
        requirement_work[0] > 0,
        "the conditional requirement was never checked at the call site: {requirement_work:?}"
    );
    assert!(
        requirement_work
            .iter()
            .all(|work| *work == requirement_work[0]),
        "conditional requirement checking grew with unrelated ambient facts: {requirement_work:?}"
    );
    assert_near_linear_scaling("specification conditional ambient facts", &samples);
}

/// A verified call publishes its callee's ensures. An ensure written as an
/// implication keeps its premises unless each is exactly available at the
/// call, so what the caller happens to know elsewhere cannot change what that
/// publication costs. The premise here is never available, the case that used
/// to end in the general prover's whole-context fallbacks; the call context
/// really does grow along this axis (9 to 66 condition facts over the four
/// sizes), while ensure publication measures 71 units at every one of them.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn verified_call_ensure_premises_ignore_unrelated_ambient_facts() {
    let mut samples = Vec::new();
    let mut ensure_work = Vec::new();
    for size in [8, 16, 32, 64] {
        let unrelated = (0..size)
            .map(|index| {
                format!(
                    "    have {index} <= count + {index} by {{\n        \
                     close() using {{\n            0 <= count;\n            \
                     count <= 1000;\n        }}\n    }}\n"
                )
            })
            .collect::<String>();
        let click_source = format!(
            "verifying \"ensure_premise_callee.c\";\n\
             verifying \"ensure_premise_scaling_caller.c\";\n\
             \n\
             int32 ensure_premise_callee(int32 flag, int32* cell) {{\n    \
                 owns cell[0..1];\n    \
                 ensures result == 0;\n    \
                 ensures flag > 0 implies cell[0] == 1;\n\
             }} by {{\n    \
                 if flag > 0 {{\n        step_until(function.exit);\n        close();\n    \
                 }} else {{\n        step_until(function.exit);\n        close();\n    }}\n\
             }}\n\
             \n\
             int32 ensure_premise_scaling_caller(int32 count, int32* cell) {{\n    \
                 requires 0 <= count;\n    \
                 requires count <= 1000;\n    \
                 owns cell[0..1];\n    \
                 ensures result == 0;\n\
             }} by {{\n{unrelated}    step_until(function.exit);\n    close();\n}}\n"
        );
        let (verified, sample) = scaling_sample(size, || {
            verify_c_sources(
                &click_source,
                &[
                    (
                        "ensure_premise_callee.c",
                        "int32 ensure_premise_callee(int32 flag, int32* cell) {\n    \
                         if (flag > 0) {\n        cell[0] = 1;\n    }\n    return 0;\n}\n",
                    ),
                    (
                        "ensure_premise_scaling_caller.c",
                        "int32 ensure_premise_scaling_caller(int32 count, int32* cell) {\n    \
                         int32 status = ensure_premise_callee(count, cell);\n    \
                         return status;\n}\n",
                    ),
                ],
            )
        });
        verified.unwrap_or_else(|error| {
            panic!(
                "size {size} ensure-premise scaling fixture failed: {}",
                error.message()
            )
        });
        ensure_work.push(
            sample
                .named_work
                .get("operation `verified call ensure lowering`")
                .copied()
                .unwrap_or(0),
        );
        samples.push(sample);
    }
    assert!(
        ensure_work[0] > 0,
        "the callee's ensures were never published at the call site: {ensure_work:?}"
    );
    assert!(
        ensure_work.iter().all(|work| *work == ensure_work[0]),
        "publishing callee ensures grew with unrelated ambient facts: {ensure_work:?}"
    );
    assert_near_linear_scaling("verified call ensure premises", &samples);
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
            "int32 scaling_identity_{index}(int32 x) {{\n    ensures result == x;\n}} by {{\n    step();\n    close();\n}}\n\n"
        ));
    }
    (c_sources, click_source)
}

fn target_with_unrelated_theorems(theorem_count: usize) -> String {
    let mut click_source = String::from("verifying \"target.c\";\n\n");
    for index in 0..theorem_count {
        click_source.push_str(&format!(
            "theorem unrelated_{index}(x: int32) {{\n    requires x == x;\n    ensures x == x by {{ close(); }}\n}}\n\n"
        ));
    }
    click_source.push_str(
        "int32 scaling_target(int32 x) {\n    ensures result == x;\n} by {\n    step();\n    close();\n}\n",
    );
    click_source
}

fn straight_line_project(statement_count: usize, program_point_claim: bool) -> (String, String) {
    let mut c_source = String::from("int32 straight_line(int32 x) {\n");
    for _ in 0..statement_count {
        c_source.push_str("    x = x;\n");
    }
    c_source.push_str("    return x;\n}\n");

    let ensure = if program_point_claim {
        "result == at(region(0).entry, x)"
    } else {
        "result == x"
    };
    let mut click_source = format!(
        "verifying \"straight.c\";\n\nint32 straight_line(int32 x) {{\n    ensures {ensure};\n}} by {{\n"
    );
    for _ in 0..=statement_count {
        click_source.push_str("    step();\n");
    }
    click_source.push_str("    close();\n}\n");
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
        LoadAxis::OneCellAcrossStores => ("owns data[0..length];", 2 * statement_count),
    };
    let mut click_source = format!(
        "verifying \"load_line.c\";\n\nint32 load_line(int32 data[], int32 length) {{\n    requires {statement_count} <= length;\n    requires 2 <= length;\n    requires (length as uint32) <= 1073741823u32;\n    {permission}\n    ensures result == data[{last}];\n}} by {{\n"
    );
    let statement_count = statements;
    for _ in 0..=statement_count + 1 {
        click_source.push_str("    step();\n");
    }
    if matches!(axis, LoadAxis::OneCellAcrossStores) {
        // The returned ownership of `owns` has no simple closer and takes the
        // one smart tactic in this fixture, before the scalar result goal.
        click_source.push_str("    close();\n");
    }
    click_source.push_str("    close();\n");
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
        "theorem exact_fact_scaling({parameters}) {{\n{requirements}    ensures target == 7 by {{ close(); }}\n}}\n"
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
        "theorem order_chain_scaling({parameters}) {{\n{requirements}    ensures low < high by {{ close(); }}\n}}\n"
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

/// `memcmp`'s byte-range precondition, which a call step's fast path leaves
/// open, proved by the written `by` body `click expand` prints for it, beside
/// `fact_count` unrelated facts about another parameter.
fn call_with_unrelated_facts(fact_count: usize) -> (String, String) {
    let c_source =
        "int32 call_target(uint8 bytes[], int32 n) {\n    return memcmp(bytes, bytes, 2);\n}\n"
            .to_string();
    let mut click_source = String::from(
        "verifying \"call_target.c\";\n\nint32 call_target(uint8 bytes[], int32 n) {\n    views bytes[0..2];\n",
    );
    for index in 0..fact_count {
        click_source.push_str(&format!("    requires n != {};\n", index + 100));
    }
    click_source.push_str(
        "    ensures 1 == 1 by {
        step() by {
            enumerate();
        }
        step();
        have 1 == 1 by {
            close();
        }
        close();
    }
}
",
    );
    (c_source, click_source)
}

/// Distinct surface forms of one kernel fact, each of constant size, so the
/// source grows linearly with `form_count`. Form `k` wraps `target` in a
/// fixed number of `+ 0` additions and the bits of `k` choose which side each
/// zero is on, so every form up to 32 is a different nesting.
fn theorem_with_many_forms(form_count: usize) -> String {
    const ADDITIONS: usize = 5;
    assert!(form_count <= 1 << ADDITIONS, "forms must stay distinct");
    let mut requirements = String::new();
    for form in 0..form_count {
        let mut expression = "target".to_string();
        for bit in 0..ADDITIONS {
            expression = if form >> bit & 1 == 1 {
                format!("(0 + {expression})")
            } else {
                format!("({expression} + 0)")
            };
        }
        requirements.push_str(&format!("    requires {expression} == 7;\n"));
    }
    format!(
        "theorem surface_form_scaling(target: int32) {{\n{requirements}    ensures target == 7 by {{ close(); }}\n}}\n"
    )
}

fn grouped_claim_project(claim_count: usize) -> (String, String) {
    let c_source = "int32 shared_claims(int32 x) { return x; }\n".to_string();
    let mut click_source =
        String::from("verifying \"shared_claims.c\";\n\nint32 shared_claims(int32 x) {\n");
    for _ in 0..claim_count {
        click_source.push_str("    ensures result == x;\n");
    }
    click_source.push_str("} by {\n    step();\n    close();\n}\n");
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
        click_source.push_str(&format!("    owns member_{index}({index});\n"));
    }
    click_source.push_str(
        "}\n\nverifying \"preserve_bundle.c\";\n\nint32 preserve_bundle(int32 p[]) {\n    views bundle(p);\n    ensures result == 0;\n} by {\n    step();\n    close();\n}\n",
    );
    (c_source, click_source)
}

pub(super) fn theorem_with_parenthesized_requirement(depth: usize) -> String {
    let opening = "(".repeat(depth);
    let closing = ")".repeat(depth);
    format!(
        "theorem nested_requirement(x: int32) {{\n    requires {opening}x + 1{closing} == x + 1;\n    ensures x == x by {{ close(); }}\n}}\n"
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
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.1s in the parallel gate"]
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
                scaling_sample(size, || verify_c_sources(&click_source, &source_refs));
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

/// Every tactic and input identity remains unchanged beside unrelated functions
/// and when verification selects only the target.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s alone, 1.3s in the parallel gate"]
fn a_functions_tactic_work_does_not_grow_with_earlier_unrelated_functions() {
    let expected = super::project_tests::combine_names_and_work(1, false);
    assert!(expected.1.iter().any(|(_, work)| *work > 0));
    for earlier in [1, 2, 4, 8] {
        for selected in [false, true] {
            assert_eq!(
                super::project_tests::combine_names_and_work(earlier, selected),
                expected,
                "earlier functions: {earlier}, selected: {selected}"
            );
        }
    }
    for selected in [false, true] {
        assert_eq!(
            super::project_tests::combine_names_and_work_in_order(8, selected, true),
            expected,
            "reordered earlier functions, selected: {selected}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn targeted_simple_verification_does_not_verify_unrelated_theorems() {
    let c_source = "int32 scaling_target(int32 x) { return x; }\n";
    let samples = [4, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let click_source = target_with_unrelated_theorems(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources_functions(
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
    // Whole-source parsing is correctly linear in the unrelated declarations;
    // the selected proof work, not that parse cost, must be independent of them.
    // Comparing total work was accidentally sensitive to whether another test
    // had already initialized the stdlib before this sample's first size.
    assert!(
        samples
            .iter()
            .all(|sample| sample.named_work == samples[0].named_work),
        "selected proof work should be insensitive to unrelated theorems: {samples:?}"
    );
}

/// A verification shares the standard library's theorem declarations; it
/// copies only its own file's. Each copied the whole library several times,
/// a fixed cost that dominated small verifications.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn verification_copies_only_its_own_theorem_declarations() {
    let c_source = "int32 scaling_target(int32 x) { return x; }\n";
    let library = standard_library_theorem_definitions()
        .expect("the standard library should load")
        .len();
    // A file's library selection is built once per process and shared, like
    // the library itself; build it before counting.
    verify_c_sources(
        &target_with_unrelated_theorems(1),
        &[("target.c", c_source)],
    )
    .expect("the warm-up target should verify");
    for size in [4, 8, 16, 32] {
        let click_source = target_with_unrelated_theorems(size);
        let before = theorem_definition_copies();
        verify_c_sources(&click_source, &[("target.c", c_source)])
            .expect("the target and its theorems should verify");
        let copies = theorem_definition_copies() - before;
        assert!(
            copies <= 4 * size,
            "{size} file theorems made {copies} theorem copies; the library has {library}"
        );
    }
}

#[test]
fn targeted_certification_keeps_an_explicit_theorem_dependency() {
    let c_source = "int32 scaling_target(int32 x) { return x; }\n";
    let click_source = r#"
        theorem equality_symmetric(first: int32, second: int32) {
            requires first == second;
            ensures second == first by { close(); }
        }

        verifying "target.c";
        int32 scaling_target(int32 x) {
            ensures x == result;
        } by {
            step();
            apply(equality_symmetric(result, x));
            close();
        }
    "#;
    verify_c_sources_functions(
        click_source,
        &[("target.c", c_source)],
        ["scaling_target".to_string()],
    )
    .expect("targeted certification should retain its applied theorem closure");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn straight_line_proof_steps_scale_near_linearly_with_retained_states() {
    for program_point_claim in [false, true] {
        let mut finalization_views = Vec::new();
        let samples = [8, 16, 32, 64]
            .into_iter()
            .map(|size| {
                let (c_source, click_source) = straight_line_project(size, program_point_claim);
                let ((verified, view_count), sample) = scaling_sample(size, || {
                    proof::count_finalization_view_constructions(|| {
                        verify_c_sources(&click_source, &[("straight.c", c_source.as_str())])
                    })
                });
                verified.unwrap_or_else(|error| {
                    panic!(
                        "size {size} straight-line fixture (state={program_point_claim}) failed: {}",
                        error.message()
                    )
                });
                finalization_views.push(view_count);
                sample
            })
            .collect::<Vec<_>>();
        assert!(
            finalization_views[0] > 0,
            "straight-line verification must exercise terminal finalization"
        );
        assert!(
            finalization_views
                .iter()
                .all(|count| *count == finalization_views[0]),
            "terminal-view construction must not grow with explicit steps: {finalization_views:?}"
        );
        assert_near_linear_scaling("straight-line proof steps", &samples);
    }
}

/// Load variables are content-addressed: constructing one, and finding the
/// same variable again for an unwritten cell in a later state, must cost work
/// proportional to the load and the steps it crosses, not to the number of
/// load variables or facts already in the proof.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.8s in the parallel gate"]
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
                    verify_c_sources(&click_source, &[("load_line.c", c_source.as_str())])
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
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn exact_known_scales_near_linearly_with_unrelated_ambient_facts() {
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

    assert_near_linear_scaling("exact known with unrelated facts", &samples);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
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
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn explicit_step_scales_near_linearly_with_unrelated_ambient_facts() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) =
                function_with_unrelated_facts(size, "    step();\n    close();\n");
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("exact_fact_target.c", c_source.as_str())])
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

/// A call step whose fast path leaves the callee's precondition open, proved
/// by a written `by` body of simple tactics and checked with the implicit
/// `solve` off, as an expanded proof is. Unrelated context facts mention the
/// same variable, so a search over the context would visit every one.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s alone (2026-10-14)"]
fn step_with_written_obligation_proof_scales_near_linearly_with_unrelated_ambient_facts() {
    let samples = [4, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = call_with_unrelated_facts(size);
            let (verified, sample) = scaling_sample(size, || {
                crate::surface::proof::without_implicit_solve(|| {
                    verify_c_sources(&click_source, &[("call_target.c", c_source.as_str())])
                })
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} written-obligation step scaling fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("step with a written obligation proof", &samples);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn explicit_return_fact_scales_near_linearly_with_unrelated_ambient_facts() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = function_with_unrelated_facts(
                size,
                "    step();\n    have result == 7 by { close(); }\n    close();\n",
            );
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("exact_fact_target.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} explicit-return-fact scaling fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("explicit return facts with unrelated facts", &samples);
}

// A cited separation rewritten through one pointer equality must not inspect
// unrelated owned cells or facts (the rbtree erase-color transport regression).
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: multi-size separation transport scaling takes 10s debug"]
fn explicit_separation_alias_transport_has_constant_selected_work() {
    let mut work = Vec::new();
    for size in [4, 16, 32, 64] {
        let resources = (0..size)
            .map(|i| {
                format!(
                    "owns background[{i}..{}]; requires background[{i}] == {i};\n",
                    i + 1
                )
            })
            .collect::<String>();
        let c = "struct node { uint64 word; struct node* left; };\nvoid inspect(struct node* parent, struct node* alias, struct node* child, int32* background) { }";
        let source = format!(
            "verifying \"alias.c\";\nvoid inspect(struct node* parent, struct node* alias, struct node* child, int32* background) {{
 owns parent->left; owns child->word; {resources}
 requires parent == alias;
 requires separate(memory(parent->left), memory(child->word));
}} by {{
 have separate(memory(alias->left), memory(child->word)) by {{
  rewrite(alias, parent);
  close();
 }}
 step_until(function.exit); close();
}}"
        );
        let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
            verify_c_sources(&source, &[("alias.c", c)])
        });
        result.unwrap_or_else(|error| panic!("{size}: {}", error.message()));
        let selected = samples
            .iter()
            .filter(|sample| sample.tactic.tactic_name == "have")
            .collect::<Vec<_>>();
        assert_eq!(selected.len(), 1);
        work.push(selected[0].work);
    }
    // Retain the flat selected-work bound across a sixteenfold change in
    // the background. The smallest fixture can cost four extra units.
    let minimum = *work.iter().min().unwrap();
    let maximum = *work.iter().max().unwrap();
    assert!(minimum > 0 && maximum - minimum <= 4, "{work:?}");
}

/// A read of a file-scope array at a symbolic index the facts place inside
/// it is one read of the array's entry run, not a case per element: the
/// split per element recursed once per cell (a thousand elements overflowed
/// the stack) and asked each case again of the cells left. What remains
/// linear in the length is the per-statement collection of the run's slot
/// variables, which a run over a block no variable names still visits slot
/// by slot.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn symbolic_index_into_a_file_scope_array_scales_near_linearly_with_its_length() {
    let samples = [512, 1024, 2048, 4096]
        .into_iter()
        .map(|size| {
            let c_source =
                format!("int32 table[{size}];\nint32 get(int32 i) {{ return table[i]; }}\n");
            let click_source = format!(
                "verifying \"table.c\";\nint32 get(int32 i) {{\n    requires 0 <= i;\n    requires i < {size};\n    requires table[i] == 7;\n    ensures result == 7;\n}}\n"
            );
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("table.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} symbolic-index table fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("symbolic index into a file-scope array", &samples);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
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
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn grouped_claims_share_one_execution_with_near_linear_work() {
    let samples = [8, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = grouped_claim_project(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("shared_claims.c", c_source.as_str())])
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

    assert_near_linear_scaling_at_sampled_sizes("claims sharing one execution", &samples);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn composite_definition_members_keep_separation_work_compact() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = resource_member_project(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("preserve_bundle.c", c_source.as_str())])
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

    // The aggregate curve also includes fixed parser and certificate costs,
    // so inspect the previously quadratic publisher directly. A zero curve
    // proves that member separation is supplied by the compact composition
    // authority instead of hidden by the fixed overhead.
    let separation_work = samples
        .iter()
        .map(|sample| {
            sample
                .named_work
                .get("operation `derived proposition: resource separate`")
                .copied()
                .unwrap_or(0)
        })
        .collect::<Vec<_>>();
    assert_eq!(
        separation_work,
        vec![0; samples.len()],
        "composite member separation must use compact composition authority, not materialized pairs"
    );
    assert_near_linear_scaling("composite definition members", &samples);
}

/// A chain of order facts stated against the context's iteration order,
/// beside unrelated facts. Premise selection indexes the context once and
/// then walks only the chain, so its fact visits are the context plus the
/// chain's own edges, however the links are ordered; growing the component
/// by repeated passes cost the whole context once per link.
#[test]
fn condition_premise_selection_walks_a_reversed_chain_once() {
    use crate::kernel::search::proposition_search::{
        condition_selection_visits, reset_condition_selection_visits,
    };
    use crate::kernel::{OldConditionTerm, OldMachineTerm, Proposition, Variable};

    let less = |left: u64, right: u64| {
        Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(OldMachineTerm::Variable(Variable(left))),
                right: Box::new(OldMachineTerm::Variable(Variable(right))),
            },
            true,
        )
    };
    let context = |links: usize, unrelated: usize, broken: Option<usize>, reversed: bool| {
        let mut available = Vec::new();
        for index in 0..unrelated {
            available.push(Proposition::condition_is(
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: Box::new(OldMachineTerm::Variable(Variable(441_000 + index as u64))),
                    right: Box::new(OldMachineTerm::constant(1_000 + index as u32)),
                },
                true,
            ));
        }
        let mut chain = (0..links)
            .filter(|link| broken != Some(*link))
            .map(|link| less(440_000 + link as u64, 440_001 + link as u64))
            .collect::<Vec<_>>();
        if reversed {
            chain.reverse();
        }
        available.extend(chain);
        available
    };
    const LINKS: usize = 3;
    let goal = less(440_000, 440_000 + LINKS as u64);
    let samples = [16usize, 32, 64, 128]
        .into_iter()
        .map(|unrelated| {
            let mut visits = Vec::new();
            let mut work = 0;
            for reversed in [false, true] {
                let available = context(LINKS, unrelated, None, reversed);
                reset_condition_selection_visits();
                let assumptions = assumptions_from_propositions(&available);
                let (derivation, units) =
                    crate::instrumentation::measure_deterministic_work(|| {
                        crate::kernel::search::ProofSearch::derive_atomic_proposition(
                            &(assumptions),
                            &goal,
                        )
                    });
                let derivation = derivation.expect("the chained order facts derive the goal");
                assert!(derivation.check(&assumptions));
                visits.push(condition_selection_visits());
                work = work.max(units);
            }
            assert_eq!(
                visits[0], visits[1],
                "selection cost depends on the order the chain was stated in"
            );
            // A missing link leaves the goal underivable.
            let broken = context(LINKS, unrelated, Some(1), true);
            assert!(
                crate::kernel::search::ProofSearch::derive_atomic_proposition(
                    &(assumptions_from_propositions(&broken)),
                    &goal
                )
                .is_none()
            );
            (unrelated, visits[0], work)
        })
        .collect::<Vec<_>>();
    // The search selects premises for a fixed number of trial contexts.
    // Each added unrelated fact is visited once per selection that sees it,
    // for the index, and never again while the chain is walked.
    for pair in samples.windows(2) {
        let added = pair[1].0 - pair[0].0;
        let visits = pair[1].1 - pair[0].1;
        assert_eq!(
            visits % added,
            0,
            "selection visits are not linear: {samples:?}"
        );
        assert!(
            visits / added <= 3,
            "selection walked the context more than once per trial: {samples:?}"
        );
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].2 <= pair[0].2.saturating_mul(3),
            "chained condition derivation is superlinear: {samples:?}"
        );
    }
}

/// One loadability goal beside growing numbers of loadability facts about
/// other objects. Source selection reads the goal's own block from the
/// kernel's index, so it examines the same candidates at every size; a scan
/// of the whole family visited every unrelated fact and tried each one.
#[test]
fn loadable_candidate_selection_ignores_facts_about_other_objects() {
    use crate::kernel::OffsetTree;
    use crate::kernel::search::proposition_search::{candidate_visits, reset_candidate_visits};
    use crate::kernel::{
        Address, AddressOffset, OldMachineTerm, Proposition, PureFactContext, SymbolicMemory,
        Variable,
    };

    let memory = SymbolicMemory::new();
    let at = |block: &str, element: u32| {
        Address::new(block.into(), AddressOffset::variable(Variable(450_000)))
            .offset_by_bytes(4 * element)
    };
    let loadable = |base: Address, bytes: u32| Proposition::MemoryLoadable {
        point: Default::default(),
        memory: memory.clone(),
        base,
        bytes: (OldMachineTerm::constant(bytes)).into(),
        wide: false,
    };
    // (sources stated about the goal's object, goal, premises the
    // certificate must cite; none when the goal must stay unproved)
    let cases = [
        (
            "one covering range",
            vec![loadable(at("goal", 0), 16)],
            loadable(at("goal", 1), 4),
            Some(1),
        ),
        (
            "two adjacent ranges",
            vec![loadable(at("goal", 0), 8), loadable(at("goal", 2), 8)],
            loadable(at("goal", 0), 16),
            Some(2),
        ),
        (
            "a gap between ranges",
            vec![loadable(at("goal", 0), 8), loadable(at("goal", 3), 4)],
            loadable(at("goal", 0), 16),
            None,
        ),
    ];
    for (name, sources, goal, cited) in cases {
        let samples = [16usize, 32, 64, 128]
            .into_iter()
            .map(|unrelated| {
                let mut context = PureFactContext::new();
                for index in 0..unrelated {
                    // The same shape as a real source, about another object.
                    context =
                        context.assume_proposition(loadable(at(&format!("other{index}"), 0), 16));
                }
                for source in &sources {
                    context = context.assume_proposition(source.clone());
                }
                reset_candidate_visits();
                let (derivation, work) = crate::instrumentation::measure_deterministic_work(|| {
                    crate::kernel::search::ProofSearch::derive_atomic_proposition(&(context), &goal)
                });
                match cited {
                    Some(cited) => {
                        let derivation =
                            derivation.unwrap_or_else(|| panic!("{name}: goal not derived"));
                        assert_eq!(
                            derivation.context_premises().len(),
                            cited,
                            "{name}: the certificate names its source facts"
                        );
                    }
                    None => assert!(derivation.is_none(), "{name}: goal derived"),
                }
                (unrelated, candidate_visits(), work)
            })
            .collect::<Vec<_>>();
        for pair in samples.windows(2) {
            assert_eq!(
                pair[0].1, pair[1].1,
                "{name}: candidate visits grew with unrelated facts: {samples:?}"
            );
            assert!(
                pair[1].2 <= pair[0].2.saturating_mul(3),
                "{name}: derivation work is superlinear: {samples:?}"
            );
        }
        assert!(samples[0].1 <= 2 * sources.len(), "{name}: {samples:?}");
    }

    // Unrelated ranges of the goal's own block are candidates, but only as
    // single sources: a goal no pair concatenates to is refused without
    // trying every pair of them.
    let samples = [16u32, 32, 64, 128]
        .into_iter()
        .map(|unrelated| {
            let mut context = PureFactContext::new()
                .assume_proposition(loadable(at("goal", 0), 8))
                .assume_proposition(loadable(at("goal", 3), 4));
            for index in 0..unrelated {
                context = context.assume_proposition(loadable(at("goal", 1_000 + 8 * index), 4));
            }
            let goal = loadable(at("goal", 0), 16);
            let (derivation, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::search::ProofSearch::derive_atomic_proposition(&(context), &goal)
            });
            assert!(derivation.is_none());
            (unrelated, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "same-block refusal is superlinear: {samples:?}"
        );
    }
}

/// Read-defined and separation goals try the sources indexed for the goal
/// before the rest of their family: a goal those sources justify examines
/// the same candidates however many unrelated facts of the family exist.
#[test]
fn read_defined_and_separation_selection_try_indexed_sources_first() {
    use crate::kernel::OffsetTree;
    use crate::kernel::search::proposition_search::{candidate_visits, reset_candidate_visits};
    use crate::kernel::{
        Address, AddressOffset, MemoryRange, OldConditionTerm, OldMachineTerm, ProgramType,
        Proposition, PureFactContext, Resource, SymbolicMemory, Variable,
    };

    let memory = SymbolicMemory::new().with_block("goal", 64);
    let read_defined = |pointer: Address| Proposition::MemoryReadDefined {
        point: Default::default(),
        at: None,
        memory: memory.clone(),
        pointer,
        value_type: ProgramType::Int32,
    };
    let at = |block: String, variable: u64| {
        Address::new(
            block.as_str().into(),
            AddressOffset::variable(Variable(variable)),
        )
    };
    let range = |base: Address, start: u32, end: u32| {
        Resource::Memory(MemoryRange::new(
            base,
            OldMachineTerm::constant(start),
            OldMachineTerm::constant(end),
        ))
    };
    let separate =
        |block: String, variable: u64, start: u32, end: u32| Proposition::ResourceSeparate {
            left: Box::new(range(at(block.clone(), variable), start, end)),
            right: Box::new(range(at(block, variable + 1), start, end)),
        };
    let address = Address::new("goal".into(), AddressOffset::constant(0));
    let alias = Address::symbolic(Variable(460_000));
    let cases: [(
        &str,
        Vec<Proposition>,
        Proposition,
        &dyn Fn(usize) -> Proposition,
    ); 2] = [
        (
            "a read defined at an alias",
            vec![
                read_defined(address.clone()),
                Proposition::condition_is(
                    OldConditionTerm::address_equal(alias.clone(), address),
                    true,
                ),
            ],
            read_defined(alias),
            &|index| {
                read_defined(Address::new(
                    format!("other{index}").as_str().into(),
                    AddressOffset::constant(0),
                ))
            },
        ),
        (
            "a separation of contained ranges",
            vec![separate("goal".to_string(), 461_000, 0, 4)],
            separate("goal".to_string(), 461_000, 1, 2),
            &|index| separate(format!("other{index}"), 462_000 + 2 * index as u64, 0, 4),
        ),
    ];
    for (name, sources, goal, unrelated_fact) in cases {
        let samples = [16usize, 32, 64, 128]
            .into_iter()
            .map(|unrelated| {
                let mut context = PureFactContext::new();
                for index in 0..unrelated {
                    context = context.assume_proposition(unrelated_fact(index));
                }
                for source in &sources {
                    context = context.assume_proposition(source.clone());
                }
                reset_candidate_visits();
                let derivation = crate::kernel::search::ProofSearch::derive_atomic_proposition(
                    &(context),
                    &goal,
                )
                .unwrap_or_else(|| panic!("{name}: goal not derived"));
                assert!(
                    derivation
                        .context_premises()
                        .iter()
                        .all(|premise| sources.contains(premise)),
                    "{name}: the certificate cites an unrelated fact"
                );
                (unrelated, candidate_visits())
            })
            .collect::<Vec<_>>();
        for pair in samples.windows(2) {
            assert_eq!(
                pair[0].1, pair[1].1,
                "{name}: candidate visits grew with unrelated facts: {samples:?}"
            );
        }
        assert!(samples[0].1 >= 1, "{name}: the indexed route was not taken");
    }
}

/// A memory goal proved from one source cites that source and the condition
/// facts connected to it, not every ambient condition: the certificate is
/// the same size however many unrelated conditions the context holds.
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
    let sampled = [
        quadratic[0].clone(),
        quadratic[2].clone(),
        quadratic[3].clone(),
    ];
    assert!(!near_linear_scaling_at_sampled_sizes(&sampled));
    assert!(named_growth_diagnostic(&quadratic).contains("quadratic reference"));
}

/// The change history is one node per recorded state. Dropping a long
/// history through the derived `Drop` recursed once per node and overflowed
/// `click verify`'s 8 MB main thread at about 6,000 recorded steps. A history
/// far longer than any budgeted proof records is dropped here on a 256 KB
/// thread, and dropped twice more with a shared suffix, since a node another
/// version still holds must stop the walk rather than be unlinked from under
/// it.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 9s in the parallel gate"]
fn recorded_state_history_drops_without_recursing() {
    let build = |size: usize| {
        let state = ExecutionState::new();
        let mut retained_states = RecordedStates::new();
        for index in 0..size {
            retained_states.insert(
                ProgramPointSelector::Mark(format!("step-{index:06}")),
                state.clone(),
            );
        }
        // Reusing an empty state must not shorten the history under test.
        let mut changes = 0;
        let mut history = retained_states.version.history.as_deref();
        while let Some(change) = history {
            changes += 1;
            history = change.parent.as_deref();
        }
        assert_eq!(changes, size);
        retained_states
    };
    std::thread::Builder::new()
        .name("recorded-state-history-drop".into())
        .stack_size(256 * 1024)
        .spawn(move || {
            drop(build(200_000));
            let shared = build(100_000);
            let mut longer = shared.clone();
            longer.insert(
                ProgramPointSelector::Mark("tip".to_string()),
                ExecutionState::new(),
            );
            drop(longer);
            assert!(shared.contains_key(&ProgramPointSelector::Mark("step-000000".to_string())));
            drop(shared);
        })
        .expect("thread")
        .join()
        .expect("dropping a recorded state history must not recurse per node");
}

#[test]
fn recorded_state_branch_merge_visits_only_fork_local_changes() {
    let mark_selector = |name: String| ProgramPointSelector::Mark(name);
    let common_selector = mark_selector("common".to_string());
    let left_only = mark_selector("left-only".to_string());
    let right_only = mark_selector("right-only".to_string());
    let common_state = ExecutionState::new();
    let mut samples = Vec::new();

    for size in [16_usize, 64, 256, 1024, 4096] {
        let mut ancestor = RecordedStates::new();
        for index in 0..size {
            ancestor.insert(
                mark_selector(format!("ambient-{index:05}")),
                ExecutionState::new(),
            );
        }
        let mut left = ancestor.clone();
        let mut right = ancestor.clone();
        left.insert(common_selector.clone(), common_state.clone());
        right.insert(common_selector.clone(), common_state.clone());
        left.insert(left_only.clone(), ExecutionState::new());
        right.insert(right_only.clone(), ExecutionState::new());

        let before = recorded_state_node_allocations();
        let merged = left
            .common_descendant(&right, &ancestor)
            .expect("fork siblings should have an exact persistent ancestor");
        let allocations = recorded_state_node_allocations() - before;
        samples.push((
            size,
            (usize::BITS - size.leading_zeros()) as usize,
            allocations,
        ));

        assert_eq!(merged.get(&common_selector), Some(&common_state));
        assert!(merged.get(&left_only).is_none());
        assert!(merged.get(&right_only).is_none());
        assert_eq!(
            merged.get(&mark_selector(format!("ambient-{:05}", size / 2))),
            Some(&ExecutionState::new())
        );
        assert_eq!(ancestor.iter().count(), size);

        let unrelated = RecordedStates::new();
        assert!(left.common_descendant(&right, &unrelated).is_none());
    }

    let (_, base_height, base_allocations) = samples[0];
    for (size, height, allocations) in samples {
        let bound = base_allocations + 8 * (height - base_height);
        assert!(
            allocations <= bound,
            "size {size} recorded-state merge allocated {allocations} nodes (logarithmic bound {bound})"
        );
    }
}

/// A ranked loop's back-edge bundle cites its arithmetic premises, so the
/// ranking members cost the same whatever else is in scope. Growing the
/// function's unrelated inequalities must not grow the work of checking that
/// the measure is nonnegative and decreases.
fn ranked_loop_with_unrelated_inequalities(fact_count: usize) -> (String, String) {
    let c_source = "int32 ranked_drain(int32 n) {\n    while (n > 0) {\n        n = n - 1;\n    }\n    return n;\n}\n".to_string();
    let mut click_source = String::from(
        "verifying \"ranked_drain.c\";\n\nint32 ranked_drain(int32 n) {\n    requires n >= 0;\n",
    );
    for index in 0..fact_count {
        click_source.push_str(&format!("    requires n != 0 - {};\n", index + 1));
    }
    click_source.push_str(
        "    ensures result == 0;\n\
         } by {\n\
         \x20   loop {\n\
         \x20       decreases n;\n\
         \x20       invariant n >= 0;\n\
         \x20       initialize by close();\n\
         \x20       maintain by {\n\
         \x20           have 0 <= n - 1 by {\n\
         \x20               close() using { n > 0; }\n\
         \x20           }\n\
         \x20           step();\n\
         \x20       }\n\
         \x20   }\n\
         \x20   step();\n\
         \x20   close();\n\
         }\n",
    );
    (c_source, click_source)
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn ranked_loop_bundle_scales_near_linearly_with_unrelated_inequalities() {
    let samples = [4, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = ranked_loop_with_unrelated_inequalities(size);
            let sources = [("ranked_drain.c", c_source.as_str())];
            let (verified, sample) =
                scaling_sample(size, || verify_c_sources(&click_source, &sources));
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} ranked-loop scaling fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling_with_increment_bound(
        "ranked loop bundle with unrelated inequalities",
        &samples,
    );
}

/// Loops ranked by a function of a binder's model, one back edge per loop.
/// Each back edge owes the measure's two members over the head and rebound
/// models; reading which binders a measure names and checking its members
/// must cost the same per loop however many other model-ranked loops the
/// project holds.
fn model_ranked_loops(loop_count: usize) -> (String, String) {
    let mut c_source = String::new();
    let mut click_source = String::from(
        "verifying \"model_ranked.c\";\n\
         \n\
         spec enum Chain { Nil, Link(Chain) }\n\
         \n\
         function chain_len(m: Chain) -> Integer\n\
         \x20   decreases m\n\
         {\n\
         \x20   match m {\n\
         \x20       Chain::Nil => 0,\n\
         \x20       Chain::Link(rest) => chain_len(rest) + 1,\n\
         \x20   }\n\
         }\n\
         \n\
         theorem chain_len_is_nonnegative(m: Chain) {\n\
         \x20   ensures 0 <= chain_len(m) by {\n\
         \x20       let ih = induct(m);\n\
         \x20       match m {\n\
         \x20           Chain::Nil => {\n\
         \x20               unfold(chain_len(Chain::Nil));\n\
         \x20               close();\n\
         \x20           }\n\
         \x20           Chain::Link(rest) => {\n\
         \x20               apply(ih(rest));\n\
         \x20               unfold(chain_len(Chain::Link(rest)));\n\
         \x20               close() using { 0 <= chain_len(rest); }\n\
         \x20           }\n\
         \x20       }\n\
         \x20   }\n\
         }\n\
         \n\
         resource chain(k: int32) {\n\
         \x20   field model: Chain;\n\
         \x20   match model {\n\
         \x20       Chain::Nil => { fact k == 0; },\n\
         \x20       Chain::Link(rest_model) => {\n\
         \x20           owns rest: chain(k - 1);\n\
         \x20           fact k > 0;\n\
         \x20           fact k - 1 >= 0;\n\
         \x20           fact rest.model == rest_model;\n\
         \x20       },\n\
         \x20   }\n\
         }\n",
    );
    for index in 0..loop_count {
        c_source.push_str(&format!(
            "void countdown{index}(int32 n) {{\n    while (n > 0) {{\n        n = n - 1;\n    }}\n}}\n\n"
        ));
        click_source.push_str(&format!(
            "\n\
             void countdown{index}(int32 n) {{\n\
             \x20   requires n >= 0;\n\
             \x20   consumes c: chain(n);\n\
             \x20   ensures 1 == 1;\n\
             }} by {{\n\
             \x20   loop {{\n\
             \x20       owns c: chain(n);\n\
             \x20       decreases chain_len(c.model);\n\
             \x20       invariant n >= 0;\n\
             \x20       initialize by close();\n\
             \x20       maintain by {{\n\
             \x20           match c.model {{\n\
             \x20               Chain::Nil => {{ close(); }},\n\
             \x20               Chain::Link(rest_model) => {{\n\
             \x20                   have chain_len(c.model) == chain_len(rest_model) + 1 by {{\n\
             \x20                       rewrite(c.model, Chain::Link(rest_model));\n\
             \x20                       unfold(chain_len(Chain::Link(rest_model)));\n\
             \x20                       close();\n\
             \x20                   }}\n\
             \x20                   apply(chain_len_is_nonnegative(rest_model));\n\
             \x20                   have chain_len(rest_model) < chain_len(c.model) by {{\n\
             \x20                       close() using {{\n\
             \x20                           chain_len(c.model) == chain_len(rest_model) + 1;\n\
             \x20                       }}\n\
             \x20                   }}\n\
             \x20                   let {{ rest: r }} = unfold(c);\n\
             \x20                   step();\n\
             \x20               }},\n\
             \x20           }}\n\
             \x20       }}\n\
             \x20   }}\n\
             \x20   have n == 0 by {{ close(); }}\n\
             \x20   unfold(c);\n\
             \x20   step();\n\
             \x20   close();\n\
             }}\n"
        ));
    }
    (c_source, click_source)
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 6s in the parallel gate"]
fn model_ranked_loops_scale_near_linearly_with_their_back_edges() {
    let samples = [2, 4, 8, 16]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = model_ranked_loops(size);
            let sources = [("model_ranked.c", c_source.as_str())];
            let (verified, sample) =
                scaling_sample(size, || verify_c_sources(&click_source, &sources));
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} model-ranked loop scaling fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling_with_increment_bound(
        "model-ranked loops by back edge count",
        &samples,
    );
}

/// One proof applying a user-defined tactic `count` times, each application
/// consuming the instance the previous one produced. An application checks
/// its binder map and the tactic's `ensures` against the proof state it is
/// given; it must cost the same whether it is the first or the hundredth.
fn repeated_tactic_applications(count: usize) -> (String, String) {
    let c_source = "struct pr { int32 a; int32 b; };\n\nvoid user(struct pr *p) {\n}\n".to_string();
    let mut click_source = String::from(
        "verifying \"applications.c\";\n\
         \n\
         resource tagged(p: struct pr*) {\n\
         \x20   field tag: int32;\n\
         \x20   owns p->a;\n\
         }\n\
         \n\
         tactic retag(p: struct pr*) {\n\
         \x20   consumes x: tagged(p);\n\
         \x20   produces y: tagged(p);\n\
         \x20   ensures y.tag == 1;\n\
         } by {\n\
         \x20   unfold(x);\n\
         \x20   let y = fold(tagged(p), { tag: 1 });\n\
         \x20   have y.tag == 1 by { close(); }\n\
         }\n\
         \n\
         void user(struct pr* p) {\n\
         \x20   consumes t0: tagged(p);\n\
         \x20   produces out: tagged(p);\n\
         } by {\n",
    );
    for index in 0..count {
        click_source.push_str(&format!(
            "    let {{ y: t{} }} = retag(p, {{ x: t{index} }});\n",
            index + 1
        ));
    }
    click_source.push_str(&format!(
        "    let {{ y: out }} = retag(p, {{ x: t{count} }});\n    step();\n    step();\n    close();\n}}\n"
    ));
    (c_source, click_source)
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn repeated_tactic_applications_scale_near_linearly() {
    let samples = [8, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = repeated_tactic_applications(size);
            let sources = [("applications.c", c_source.as_str())];
            let (verified, sample) =
                scaling_sample(size, || verify_c_sources(&click_source, &sources));
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} repeated tactic application fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling_at_sampled_sizes("repeated tactic applications", &samples);
}

/// The same ranked loop closed by the back edge's smart closer.
/// The planner's candidate premises are the loop head's clauses and the
/// contract's own requirements, so growing the function's unrelated
/// inequalities must grow the closure's work no faster than the clauses it
/// has to classify: a scan of the ambient fact context would not stay here.
fn smart_ranked_loop_with_unrelated_inequalities(fact_count: usize) -> (String, String) {
    let c_source = "int32 ranked_drain(int32 n) {\n    while (n > 0) {\n        n = n - 1;\n    }\n    return n;\n}\n".to_string();
    let mut click_source = String::from(
        "verifying \"ranked_drain.c\";\n\nint32 ranked_drain(int32 n) {\n    requires n >= 0;\n",
    );
    for index in 0..fact_count {
        click_source.push_str(&format!("    requires n != 0 - {};\n", index + 1));
    }
    click_source.push_str(
        "    ensures result == 0;\n\
         } by {\n\
         \x20   loop {\n\
         \x20       decreases n;\n\
         \x20       invariant n >= 0;\n\
         \x20       initialize by close();\n\
         \x20       maintain by {\n\
         \x20           have 0 <= n - 1 by {\n\
         \x20               close() using { n > 0; }\n\
         \x20           }\n\
         \x20           step();\n\
         \x20       }\n\
         \x20   }\n\
         \x20   step();\n\
         \x20   close();\n\
         }\n",
    );
    (c_source, click_source)
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn smart_ranked_loop_bundle_scales_near_linearly_with_unrelated_inequalities() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = smart_ranked_loop_with_unrelated_inequalities(size);
            let sources = [("ranked_drain.c", c_source.as_str())];
            let (verified, sample) =
                scaling_sample(size, || verify_c_sources(&click_source, &sources));
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} smart ranked-loop scaling fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling(
        "smart ranked loop bundle with unrelated inequalities",
        &samples,
    );
}

/// A loop whose one invariant declaration has `conjuncts` members, each an
/// `int32` addition under a definedness guard. The back-edge bundle is those
/// guards introduced over the member chain, beside the ranking pair; the body
/// states every member, so each leaf closes by a direct step.
fn guarded_member_bundle(conjuncts: usize) -> (String, String) {
    let c_source = "int32 guarded_bundle(int32 n) {\n    int32 i = 0;\n\n    while (i < n) {\n        i = i + 1;\n    }\n    return i;\n}\n".to_string();
    let members = (1..=conjuncts)
        .map(|k| format!("(i <= n or {k} + i == 0)"))
        .collect::<Vec<_>>()
        .join(" and\n            ");
    let facts = (1..=conjuncts)
        .map(|k| format!("            have i <= n or {k} + i == 0 by {{ close(); }}\n"))
        .collect::<String>();
    let click_source = format!(
        "verifying \"guarded_bundle.c\";\n\n\
         int32 guarded_bundle(int32 n) {{\n\
         \x20   requires 0 <= n;\n\
         \x20   ensures result == n;\n\
         }} by {{\n\
         \x20   step();\n\
         \x20   step();\n\
         \x20   loop {{\n\
         \x20       decreases n - i;\n\
         \x20       invariant 0 <= i and i <= n;\n\
         \x20       invariant {members};\n\
         \x20       initialize by close();\n\
         \x20       maintain by {{\n\
         \x20           mark iteration;\n\
         \x20           have 0 <= at(iteration, i) by {{ close(); }}\n\
         \x20           step();\n\
         \x20           have 0 <= i by {{ close(); }}\n\
         \x20           have i <= n by {{ close(); }}\n\
         \x20           have 0 <= i and i <= n by {{ close(); }}\n\
         {facts}\
         \x20           have 0 <= n - at(iteration, i) - 1 by {{\n\
         \x20               close() using {{\n\
         \x20                   0 <= at(iteration, i);\n\
         \x20                   at(iteration, i) < at(iteration, n);\n\
         \x20                   0 <= n;\n\
         \x20               }}\n\
         \x20           }}\n\
         \x20           have n - at(iteration, i) - 1 < n - at(iteration, i) by {{\n\
         \x20               close() using {{\n\
         \x20                   0 <= at(iteration, i);\n\
         \x20                   at(iteration, i) < at(iteration, n);\n\
         \x20                   0 <= n;\n\
         \x20               }}\n\
         \x20           }}\n\
         \x20       }}\n\
         \x20   }}\n\
         \x20   step();\n\
         \x20   close();\n\
         }}\n"
    );
    (c_source, click_source)
}

/// The back edge closes a bundle whose conjuncts sit under guards with
/// the direct logical steps alone, so its work follows the bundle's size.
/// Before, the closer ran the premise-selecting and rewriting strategies over
/// the whole bundle and every suffix of it first, and four guarded members
/// already exhausted the smart budget.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn smart_guarded_member_bundle_scales_near_linearly_with_conjuncts() {
    let samples = [2, 4, 8, 16]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = guarded_member_bundle(size);
            let sources = [("guarded_bundle.c", c_source.as_str())];
            let (verified, sample) =
                scaling_sample(size, || verify_c_sources(&click_source, &sources));
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} guarded-member bundle fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();
    assert_near_linear_scaling("guarded invariant members", &samples);
    let closer = samples
        .iter()
        .map(|sample| ScalingSample {
            size: sample.size,
            work: sample
                .named_work
                .get("operation `close invariants: members`")
                .copied()
                .unwrap_or(0),
            named_work: BTreeMap::new(),
        })
        .collect::<Vec<_>>();
    assert!(closer.iter().all(|sample| sample.work > 0), "{closer:?}");
    assert_near_linear_scaling("back-edge closure over guarded members", &closer);
}

/// [`guarded_member_bundle`] with each member in an `invariant` declaration
/// of its own, so the back-edge bundle guards each member by every earlier
/// declaration.
fn separately_declared_member_bundle(declarations: usize) -> (String, String) {
    let (c_source, click_source) = guarded_member_bundle(declarations);
    let joined = (1..=declarations)
        .map(|k| format!("(i <= n or {k} + i == 0)"))
        .collect::<Vec<_>>()
        .join(" and\n            ");
    let separate = (1..=declarations)
        .map(|k| format!("i <= n or {k} + i == 0"))
        .collect::<Vec<_>>()
        .join(";\n        invariant ");
    assert!(click_source.contains(&joined));
    (c_source, click_source.replace(&joined, &separate))
}

/// A bundle of separately declared invariants is a chain of guards per
/// member, quadratic in the declarations by construction. Spelling its
/// members keys each written invariant and each distinct guard once, so the
/// closer's work stays within that size. Before, every member compared every
/// suffix of its guard chain with every written form, rebuilding both keys
/// each time, and 28 declarations of a real proof exhausted the smart budget
/// with every member already an available fact.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 22s focused, separately declared invariant scaling audit"]
fn back_edge_closure_over_separately_declared_invariants_is_bounded_by_the_bundle() {
    let closer = [8, 16, 32]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = separately_declared_member_bundle(size);
            let sources = [("guarded_bundle.c", c_source.as_str())];
            let (verified, sample) =
                scaling_sample(size, || verify_c_sources(&click_source, &sources));
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} separately declared bundle fixture failed: {}",
                    error.message()
                )
            });
            sample
                .named_work
                .get("operation `close invariants: members`")
                .copied()
                .unwrap_or(0)
        })
        .collect::<Vec<_>>();
    assert!(closer.iter().all(|work| *work > 0), "{closer:?}");
    // Each doubling adds work in proportion to the declarations it adds;
    // the per-suffix comparison added several times that.
    let (first, second) = (closer[1] - closer[0], closer[2] - closer[1]);
    assert!(second < first * 3, "{closer:?}");
}

/// A caller with growing unrelated facts calling a callee whose precondition
/// has logical structure.
///
/// The kernel's exact routes do not cover the disjunction, so the call raises
/// it as a required verification condition on every size. The point of the
/// measurement is that raising and discharging it costs what the requirement
/// and the one cited arm cost, not what the caller's fact context costs.
fn call_with_structured_precondition(fact_count: usize) -> (String, String) {
    let c_source =
        "int32 structured_precondition_caller(int32 x, int32 y) {\n    int32 result;\n    result = either_positive(x, y);\n    return result;\n}\n"
            .to_string();
    let mut click_source = String::from(
        "verifying \"structured_precondition_caller.c\";\n\nextern int32 either_positive(int32 x, int32 y) {\n    requires x > 0 or y > 0;\n    ensures result == 0;\n}\n\nint32 structured_precondition_caller(int32 x, int32 y) {\n    requires x > 0;\n",
    );
    for index in 0..fact_count {
        click_source.push_str(&format!("    requires y != {};\n", index + 100));
    }
    click_source.push_str("    ensures result == 0;\n}\n");
    (c_source, click_source)
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn call_requirement_checking_scales_near_linearly_with_unrelated_caller_facts() {
    let samples = [4, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = call_with_structured_precondition(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(
                    &click_source,
                    &[("structured_precondition_caller.c", c_source.as_str())],
                )
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} call-requirement scaling fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling_with_increment_bound(
        "call requirement checking with unrelated caller facts",
        &samples,
    );
}

/// A project written entirely in explicit simple tactics must verify in work
/// approximately linear in its own source while unrelated ambient facts grow
/// alongside it.
///
/// This is package 15's acceptance regression. Before the proposition search
/// left the kernel, every miss in an authoritative kernel route ran the
/// general prover, whose whole-context fallbacks (the inconsistency scan and
/// singleton substitution) read every ambient fact on every failed query. A
/// project like this one -- `size` statements, each closed by its own
/// `step()`, under `size` unrelated requirements the proof never cites --
/// grew both axes at once, so that scan was charged once per query per fact.
/// The retained exact routes read the index the goal names and nothing else.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn explicit_simple_tactics_scale_with_source_while_ambient_facts_grow() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = explicit_simple_project_with_ambient_facts(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("straight.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} explicit simple-tactic project failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling(
        "explicit simple tactics with growing source and ambient facts",
        &samples,
    );
}

/// `size` assignments closed by one explicit `step()` each, under `size`
/// unrelated `requires` the proof never mentions. Both the selected source
/// and the ambient fact set grow with `size`.
fn explicit_simple_project_with_ambient_facts(size: usize) -> (String, String) {
    let (c_source, base_click) = straight_line_project(size, false);
    // Unrelated ambient facts: true of the argument, never cited by the
    // proof, and disjoint from the equality the claim needs.
    let unrelated = (0..size)
        .map(|index| format!("    requires x != {};\n", index + 1000))
        .collect::<String>();
    let click_source = base_click.replacen(
        "    ensures result == x;\n",
        &format!("{unrelated}    ensures result == x;\n"),
        1,
    );
    assert_ne!(
        click_source, base_click,
        "the ambient facts were not inserted"
    );
    (c_source, click_source)
}

/// An N-constructor execution `match` must cost its N arms.
///
/// A wide match is joined by a chain of two-way group splits, so a deferred
/// post-execution operation reaches the join as a nested `if` tree whose
/// conditions select constructor subsets. Serializing that tree back into the
/// lexical arms only recognized the two-constructor selector, so every wider
/// match cloned the complete N-leaf tree into each of its N arms. The retained
/// certificate was therefore quadratic in the width, and it was rebuilt and
/// then structurally compared once per certified path and claim, which grew a
/// debug `click verify` about thirteen times per doubling.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 6s in the parallel gate"]
fn wide_execution_match_join_has_near_linear_width_work() {
    let mut samples = Vec::new();
    let mut certificate_sizes = Vec::new();
    for width in [2, 4, 8, 16] {
        let (click_source, c_source) = wide_execution_match_project(width);
        let (verified, sample) = scaling_sample(width, || {
            verify_c_sources(&click_source, &[("read.c", c_source.as_str())])
        });
        let verified = verified.unwrap_or_else(|error| {
            panic!(
                "width {width} execution match failed: {}",
                error.message().replace('\n', " ")
            )
        });
        let certificate = verified
            .first()
            .and_then(|theorem| theorem.expanded_proof.as_ref())
            .unwrap_or_else(|| panic!("width {width} retained no certificate"));
        // Every certified path and claim retains the one certificate this
        // proof produced. Rebuilding it per theorem instead made both the
        // clone and the later theorem-set comparison pay its full size.
        assert!(
            verified.iter().all(|theorem| theorem
                .expanded_proof
                .as_ref()
                .is_some_and(|retained| retained.shares_steps_with(certificate))),
            "width {width} rebuilt the retained certificate per theorem"
        );
        certificate_sizes.push((width, certificate_step_count(certificate.steps())));
        samples.push(sample);
    }
    // The certificate is this join's own output, and one arm's operations
    // belong to that arm alone, so the whole match stays linear in its
    // constructor count: doubling the width may double the certificate, never
    // square it.
    for pair in certificate_sizes.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 5 / 2,
            "the retained certificate grows faster than the constructor count: {certificate_sizes:?}"
        );
    }
    // Preserve the old certificate curvature crossover at 16/32 while
    // removing the fixed certificate overhead from the smaller 4/8/16 grid.
    assert_bounded_work_increments(
        "retained wide-match certificate",
        &certificate_sizes
            .iter()
            .map(|(_, steps)| *steps)
            .collect::<Vec<_>>(),
        12,
        5,
    );
    assert_near_linear_scaling_with_increment_bound("wide execution match join", &samples);
}

/// Counts every step of a certificate, including those its structured steps
/// own, so a certificate that re-emits a join tree inside each arm is
/// distinguishable from one that does not.
fn certificate_step_count(steps: &[ProofStep]) -> usize {
    fn nested(step: &ProofStep) -> usize {
        1 + match step {
            ProofStep::Match { arms, .. } => arms
                .iter()
                .map(|arm| certificate_step_count(arm.proof.steps()))
                .sum(),
            ProofStep::CloseInvariantsBy(proof) => certificate_step_count(proof.steps()),
            ProofStep::Both {
                left_proof,
                right_proof,
                ..
            }
            | ProofStep::Cases {
                left_proof,
                right_proof,
                ..
            } => {
                certificate_step_count(left_proof.steps())
                    + certificate_step_count(right_proof.steps())
            }
            ProofStep::If {
                then_proof,
                else_proof,
                ..
            }
            | ProofStep::Branch {
                then_proof,
                else_proof,
                ..
            } => {
                certificate_step_count(then_proof.steps())
                    + certificate_step_count(else_proof.steps())
            }
            ProofStep::Have { proof, .. } | ProofStep::Open { proof, .. } => {
                certificate_step_count(proof.steps())
            }
            _ => 0,
        }
    }
    steps.iter().map(nested).sum()
}

/// A `width`-constructor model over one cell, read by one C load, proved by a
/// proof `match` whose arms are identical up to the constant each constructor
/// carries. Only the constructor count varies with `width`: the C source, the
/// contract shape, and each arm's proof are fixed.
fn wide_execution_match_project(width: usize) -> (String, String) {
    let variants = (0..width)
        .map(|index| format!("V{index}"))
        .collect::<Vec<_>>()
        .join(", ");
    let code_arms = (0..width)
        .map(|index| format!("        Wide::V{index} => {index},\n"))
        .collect::<String>();
    let resource_arms = (0..width)
        .map(|index| {
            format!("        Wide::V{index} => {{ owns p[0..1]; fact p[0] == {index}; }},\n")
        })
        .collect::<String>();
    let proof_arms = (0..width)
        .map(|index| {
            format!(
                "        Wide::V{index} => {{\n\
                 \x20           unfold(c);\n\
                 \x20           step_until(function.exit);\n\
                 \x20           let c = fold(cell(p), {{ model: Wide::V{index} }});\n\
                 \x20           have wide_code(old(c.model)) == {index} by {{\n\
                 \x20               rewrite(old(c.model), Wide::V{index});\n\
                 \x20               unfold(wide_code(Wide::V{index}));\n\
                 \x20               close();\n\
                 \x20           }}\n\
                 \x20           close();\n\
                 \x20       }},\n"
            )
        })
        .collect::<String>();
    let click_source = format!(
        "verifying \"read.c\";\n\
         \n\
         spec enum Wide {{ {variants} }}\n\
         \n\
         function wide_code(q: Wide) -> int32 {{\n\
         \x20   match q {{\n{code_arms}\x20   }}\n\
         }}\n\
         \n\
         resource cell(p: int32*) {{\n\
         \x20   field model: Wide;\n\
         \x20   match model {{\n{resource_arms}\x20   }}\n\
         }}\n\
         \n\
         int32 read(int32* p) {{\n\
         \x20   owns c: cell(p);\n\
         \x20   ensures c.model == old(c.model);\n\
         \x20   ensures result == wide_code(old(c.model));\n\
         }} by {{\n\
         \x20   match c.model {{\n{proof_arms}\x20   }}\n\
         }}\n"
    );
    (
        click_source,
        "int32 read(int32* p) { return *p; }".to_string(),
    )
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.8s in the parallel gate"]
fn outcome_haves_and_resource_folds_do_not_reimport_ambient_facts() {
    assert_outcome_operations_do_not_reimport_ambient_facts(|source, sources| {
        verify_c_sources(source, sources).map(|_| ())
    });
}

/// An outcome unfold is retained on the completed
/// path, so the path's completion checks the retained `have` proofs. Facts
/// the proof held at its checked entry are not checked again.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.9s in the parallel gate"]
fn authority_outcome_haves_and_resource_folds_do_not_reimport_ambient_facts() {
    assert_outcome_operations_do_not_reimport_ambient_facts(|source, sources| {
        let project = ClickProject::new(
            "identity.click",
            [ClickModuleSource::new("identity.click", source, [])],
        )
        .with_c_profile(CProjectProfile {
            target: None,
            runtime: None,
        });
        verify_c_project(&project, sources).map(|_| ())
    });
}

fn assert_outcome_operations_do_not_reimport_ambient_facts(
    verify: impl Fn(&str, &[(&str, &str)]) -> Result<(), ClickError>,
) {
    let c_source = "int32 identity(int32 x) { return x; }";
    let mut samples = Vec::new();
    for size in [8_usize, 16, 32, 64] {
        let requirements = (0..size)
            .map(|i| format!("requires x != {i};"))
            .collect::<String>();
        let mut baseline = None;
        for operations in [0_usize, 1, 4, 16] {
            // Include one operation in every sample. The first retained
            // operation starts the outcome proof, so use the next operation
            // to measure the cost of extending that proof.
            let body = (0..=operations)
                .map(|i| {
                    format!(
                        "have to_integer(x) < {} by {{ close(); }} unfold(marker(x)); fold(marker(x));",
                        2147483648_u64 + i as u64,
                    )
                })
                .collect::<String>();
            let source = format!(
                r#"
                resource marker(x: int32) {{ fact x == x; }}
                verifying "identity.c";
                int32 identity(int32 x) {{
                    {requirements}
                    owns marker(x);
                    ensures result == x;
                }} by {{ step_until(function.exit); {body} close(); }}
            "#
            );
            crate::kernel::proof::take_fact_entry_counts();
            verify(&source, &[("identity.c", c_source)]).unwrap_or_else(|error| {
                panic!("ambient {size}, operations {operations}: {error:?}")
            });
            let (indexed, materialized) = crate::kernel::proof::take_fact_entry_counts();
            let (base_indexed, base_materialized) =
                *baseline.get_or_insert((indexed, materialized));
            samples.push((
                size,
                operations,
                indexed - base_indexed,
                materialized - base_materialized,
            ));
        }
    }
    for operations in [1, 4, 16] {
        let curve = samples
            .iter()
            .filter(|sample| sample.1 == operations)
            .collect::<Vec<_>>();
        assert!(
            curve[0].2 > 0,
            "the regression must exercise checked fact production"
        );
        for sample in &curve[1..] {
            assert_eq!(
                (sample.2, sample.3),
                (curve[0].2, curve[0].3),
                "unrelated input facts changed the cost of the outcome operations: {samples:?}"
            );
        }
    }
    let unit = samples
        .iter()
        .find(|sample| sample.0 == 8 && sample.1 == 1)
        .unwrap();
    for sample in samples
        .iter()
        .filter(|sample| sample.0 == 8 && sample.1 > 0)
    {
        assert!(
            sample.2 <= unit.2 * sample.1 && sample.3 <= unit.3 * sample.1,
            "outcome operation history grew faster than its produced deltas: {samples:?}"
        );
    }
}

/// A maybe-throwing call is the shared control-flow boundary used by the C++
/// cleanup lowering.  The returned arm advances through the selected cleanup
/// chain; the thrown arm must retain its exceptional outcome without executing
/// the normal-only tail.  The unrelated declarations and requirements make
/// sure the boundary is charged for its selected frontier, not for every
/// function, scope, or fact in the enclosing verification.
fn exceptional_cleanup_chain_project(
    cleanup_count: usize,
    unrelated_function_count: usize,
    unrelated_fact_count: usize,
) -> (String, String) {
    let mut c_source = String::from("int32 helper(int32 x) { return x; }\n\n");
    for index in 0..cleanup_count {
        c_source.push_str(&format!("int32 cleanup_{index}(int32 x) {{ return x; }}\n"));
    }
    for index in 0..unrelated_function_count {
        c_source.push_str(&format!(
            "int32 unrelated_{index}(int32 x) {{ return x; }}\n"
        ));
    }
    c_source.push_str("\nint32 cleanup_caller(int32 x) {\n    int32 result = helper(x);\n");
    for index in 0..cleanup_count {
        c_source.push_str(&format!("    result = cleanup_{index}(result);\n"));
    }
    c_source.push_str("    return result;\n}\n");

    // These facts must not name x: result == x merges would then have to
    // update their predicate signatures, making them relevant to each call.
    let mut click_source = String::from(
        "verifying \"cleanup.c\";\n\nfunction unrelated_fact(n: int32) -> int32 { n }\n\n",
    );
    click_source.push_str(
        "int32 helper(int32 x) throws int32 {\n    ensures result == x;\n    exceptional ensures exception == 7;\n}\n\n",
    );
    for index in 0..cleanup_count {
        click_source.push_str(&format!(
            "int32 cleanup_{index}(int32 x) {{\n    ensures result == x;\n}}\n\n"
        ));
    }
    for index in 0..unrelated_function_count {
        click_source.push_str(&format!(
            "int32 unrelated_{index}(int32 x) {{ ensures result == x; }}\n\n"
        ));
    }
    click_source.push_str("int32 cleanup_caller(int32 x) throws int32 {\n");
    for index in 0..unrelated_fact_count {
        click_source.push_str(&format!(
            "    requires unrelated_fact({}) != 0;\n",
            10_000 + index
        ));
    }
    click_source.push_str("    ensures result == x;\n    exceptional ensures exception == 7;\n}\n");
    (c_source, click_source)
}

/// The C++ importer currently emits a bounded cleanup list, but its cleanup
/// calls use the same checked outcome frontier as this growing C model.  This
/// acceptance regression keeps that shared engine honest while the selected
/// cleanup-edge count grows from 2 through 16 and unrelated scopes/functions/
/// facts grow with it.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.1s in the parallel gate"]
fn exceptional_cleanup_edges_scale_near_linearly_with_unrelated_context() {
    const CALL_WORK: &str = "operation `verification statement: call`";
    let mut samples = Vec::new();
    let mut cleanup_work = Vec::new();
    for size in [2, 8, 16] {
        let (c_source, click_source) = exceptional_cleanup_chain_project(size, size, size);
        let (verified, sample) = scaling_sample(size, || {
            verify_c_sources(&click_source, &[("cleanup.c", c_source.as_str())])
        });
        verified.unwrap_or_else(|error| {
            panic!(
                "size {size} exceptional cleanup scaling fixture failed: {}",
                error.message()
            )
        });
        cleanup_work.push(sample.named_work.get(CALL_WORK).copied().unwrap_or(0));
        samples.push(sample);
    }
    assert!(
        cleanup_work[0] > 0,
        "the scaling fixture never checked the exceptional frontier: {cleanup_work:?}"
    );
    assert_near_linear_scaling_at_sampled_sizes("exceptional cleanup edges", &samples);
    assert_near_linear_scaling_at_sampled_sizes(
        "exceptional cleanup call frontier",
        &samples
            .iter()
            .map(|sample| ScalingSample {
                size: sample.size,
                work: *sample.named_work.get(CALL_WORK).unwrap_or(&0),
                named_work: BTreeMap::new(),
            })
            .collect::<Vec<_>>(),
    );

    // Hold the selected edge and cleanup count fixed while unrelated function
    // scopes and facts grow. The named call work must not inspect those
    // unrelated declarations to re-check the same frontier.
    let mut fixed_cleanup_work = Vec::new();
    // Preserve the original unrelated-context endpoints and exact selected-work equality.
    for unrelated in [4, 32] {
        let (c_source, click_source) = exceptional_cleanup_chain_project(8, unrelated, unrelated);
        let (verified, sample) = scaling_sample(8, || {
            verify_c_sources(&click_source, &[("cleanup.c", c_source.as_str())])
        });
        verified.unwrap_or_else(|error| {
            panic!(
                "unrelated context {unrelated} fixed-frontier fixture failed: {}",
                error.message()
            )
        });
        fixed_cleanup_work.push(sample.named_work.get(CALL_WORK).copied().unwrap_or(0));
    }
    assert!(
        fixed_cleanup_work
            .iter()
            .all(|work| *work == fixed_cleanup_work[0]),
        "fixed cleanup frontier work changed with unrelated context: {fixed_cleanup_work:?}"
    );
}

/// One project with `statement_count` local stores between two uses of the
/// same fact about an array the stores cannot touch.
fn array_fact_across_local_stores(statement_count: usize, observe_each: bool) -> (String, String) {
    let mut c_source = String::from("void bump(int32 a[], int32 n) {\n    int32 i;\n    i = 0;\n");
    for _ in 0..statement_count {
        c_source.push_str("    i = i + 1;\n");
    }
    c_source.push_str("}\n");

    let mut click_source = String::from(
        "verifying \"bump.c\";\n\nfunction icount(p: int32[], lo: int32, hi: int32) -> Integer {\n    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })\n}\n\nvoid bump(int32 a[], int32 n) {\n    requires 0 < n;\n    requires viewable(a[0..n]);\n    views a[0..n];\n} by {\n    step();\n    step();\n    have 0 <= 0 by { close(); }\n    have icount(a, 0, 0) == 0 by {\n        unfold(icount(a, 0, 0));\n        close();\n    }\n",
    );
    // One use of the fact after every step: the walk is asked from a fresh
    // state each time, which is the shape that goes quadratic when an
    // version walk cannot reuse the answer it computed one state ago.
    for _ in 0..statement_count {
        click_source.push_str("    step();\n");
        if observe_each {
            click_source.push_str("    have icount(a, 0, 0) == 0 by { close(); }\n");
        }
    }
    if !observe_each {
        click_source.push_str("    have icount(a, 0, 0) == 0 by { close(); }\n");
    }
    click_source.push_str("    step_until(function.exit);\n    close();\n}\n");
    (c_source, click_source)
}

/// One project with `statement_count` bare declarations between two uses of
/// the same fact about an array no declaration can touch.
fn array_fact_across_declarations(statement_count: usize) -> (String, String) {
    let mut c_source = String::from("void bump(int32 a[], int32 n) {\n");
    for index in 0..statement_count {
        c_source.push_str(&format!("    int32 t{index};\n"));
    }
    c_source.push_str("}\n");

    let mut click_source = String::from(
        "verifying \"bump.c\";\n\nfunction icount(p: int32[], lo: int32, hi: int32) -> Integer {\n    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })\n}\n\nvoid bump(int32 a[], int32 n) {\n    requires 0 < n;\n    requires viewable(a[0..n]);\n    views a[0..n];\n} by {\n    have 0 <= 0 by { close(); }\n    have icount(a, 0, 0) == 0 by {\n        unfold(icount(a, 0, 0));\n        close();\n    }\n",
    );
    for _ in 0..statement_count {
        click_source.push_str("    step();\n");
        click_source.push_str("    have icount(a, 0, 0) == 0 by { close(); }\n");
    }
    click_source.push_str("    step_until(function.exit);\n    close();\n}\n");
    (c_source, click_source)
}

/// One project with `statement_count` calls that may write only another
/// object, between two uses of the same fact about `h`.
fn array_fact_across_calls(statement_count: usize) -> (String, String) {
    let mut c_source = String::from(
        "int32 g[4];\nint32 h[4];\n\nvoid touch_g() {\n    g[0] = 1;\n}\n\nint32 keep_h() {\n",
    );
    for _ in 0..statement_count {
        c_source.push_str("    touch_g();\n");
    }
    c_source.push_str("    return h[0];\n}\n");

    let mut click_source = String::from(
        "verifying \"keep_h.c\";\n\nfunction icount(p: int32[], lo: int32, hi: int32) -> Integer {\n    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })\n}\n\nvoid touch_g() {\n    owns g[0..1];\n}\n\nint32 keep_h() {\n    requires h[0] == 5;\n    owns g[0..1];\n    views h[0..1];\n    ensures result == 5;\n} by {\n    have 0 <= 0 by { close(); }\n    have icount(h, 0, 0) == 0 by {\n        unfold(icount(h, 0, 0));\n        close();\n    }\n",
    );
    for _ in 0..statement_count {
        click_source.push_str("    step();\n");
        click_source.push_str("    have icount(h, 0, 0) == 0 by { close(); }\n");
    }
    click_source.push_str("    step_until(function.exit);\n    close();\n}\n");
    (c_source, click_source)
}

/// Array-version selection work across one fixture family. Each fixture
/// must exercise its selected operation.
fn array_version_work_curve(
    label: &str,
    file: &str,
    operation: &str,
    fixture: impl Fn(usize) -> (String, String),
) -> Vec<ScalingSample> {
    [2, 4, 8, 16]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = fixture(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[(file, c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!("size {size} {label} fixture failed: {}", error.message())
            });
            ScalingSample {
                size: sample.size,
                work: *sample
                    .named_work
                    .get(operation)
                    .unwrap_or_else(|| panic!("fixture did not reach {operation}: {sample:?}")),
                named_work: BTreeMap::new(),
            }
        })
        .collect()
}

/// Repeated array references use indexed versions across two kinds of
/// disjoint effects: declarations for a parameter array and checked call
/// footprints for a static array.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn an_array_fact_carried_across_declarations_and_calls_scales_linearly() {
    assert_near_linear_scaling(
        "array-ref indexed version across declarations",
        &array_version_work_curve(
            "array-fact-across-declarations",
            "bump.c",
            "operation `array-ref indexed version`",
            array_fact_across_declarations,
        ),
    );
    assert_near_linear_scaling(
        "array-ref indexed static version across calls",
        &array_version_work_curve(
            "array-fact-across-calls",
            "keep_h.c",
            "operation `array-ref indexed version`",
            array_fact_across_calls,
        ),
    );
}

/// Each use of an array fact across disjoint local stores selects the same
/// entry version through the recorded path index.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn an_array_fact_carried_across_local_stores_scales_linearly() {
    let samples = [4, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = array_fact_across_local_stores(size, true);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("bump.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} array-fact scaling fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("array fact across unrelated local stores", &samples);

    const INDEXED_VERSION: &str = "operation `array-ref indexed version`";
    let naming = samples
        .iter()
        .map(|sample| ScalingSample {
            size: sample.size,
            work: *sample.named_work.get(INDEXED_VERSION).unwrap_or_else(|| {
                panic!("fixture did not use the array version index: {sample:?}")
            }),
            named_work: BTreeMap::new(),
        })
        .collect::<Vec<_>>();
    assert_near_linear_scaling("array-ref indexed version", &naming);
}

/// The first array read after a long run of disjoint statements must not
/// traverse that run. Per-statement lookups can hide this behind memo hits.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn one_array_lookup_after_disjoint_local_stores_has_bounded_work() {
    let work = [4, 16, 64].map(|size| {
        let (c, source) = array_fact_across_local_stores(size, false);
        let (verified, events) =
            crate::instrumentation::collect(|| verify_c_sources(&source, &[("bump.c", &c)]));
        verified.unwrap_or_else(|error| panic!("size {size}: {}", error.message()));
        events
            .into_iter()
            .filter_map(|event| match event {
                crate::instrumentation::VerificationEvent::OperationFinished {
                    name, work, ..
                } if name == "array-ref block version walk" => Some(work),
                _ => None,
            })
            .max()
            .unwrap_or(0)
    });
    assert!(work.iter().all(|sample| *sample <= work[0]), "{work:?}");
}

/// One project with `size` stores made while `size` owned ranges are held, so
/// that every store's per-cell drop is asked about a composition with `size`
/// members.
///
/// This is the shape that pays for
/// `memory_history::owned_composition_store_separated_evidence`: it runs
/// per surviving cell per store, and looks each side up in the composition's
/// own block bucket, so a context holding many owned ranges is exactly where
/// a per-member scan would show.
fn stores_beside_many_owned_ranges(size: usize) -> (String, String) {
    let mut c_source = String::from(
        "int32* read_acquired(int32* (*acquire)(), int32* value) {\n    int32* cell = acquire();\n    if (cell != 0) {\n",
    );
    for index in 0..size {
        c_source.push_str(&format!("        value[{index}] = *cell;\n"));
    }
    c_source.push_str("    }\n    return cell;\n}\n");

    let mut click_source = String::from(
        "resource MaybeRaw(p: int32*) {\n    if p != 0 {\n        owns p[0..1];\n    }\n}\nresource Cell(p: int32*) {\n    owns p[0..1];\n}\nresource MaybeCell(p: int32*) {\n    if p != 0 { owns Cell(p); }\n}\ncontract int32* Raw() {\n    produces MaybeRaw(result);\n}\ncontract int32* Boxed() {\n    produces MaybeCell(result);\n}\ntheorem lift(acquire: int32* (*)()) executes acquire() {\n    requires Raw(acquire);\n    ensures Boxed(acquire) by {\n        step(Raw);\n        if result != 0 {\n            unfold(MaybeRaw(result));\n            fold(Cell(result));\n            fold(MaybeCell(result));\n            close();\n        } else {\n            unfold(MaybeRaw(result));\n            fold(MaybeCell(result));\n            close();\n        }\n    }\n}\nverifying \"acquire.c\";\nint32* read_acquired(int32* (*acquire)(), int32* value) {\n    requires Raw(acquire);\n",
    );
    click_source.push_str(&format!("    owns value[0..{size}];\n"));
    // One claim, not one per store: the fixture is here to measure the
    // per-store composition query, and `size` claims about `size` stores
    // would be quadratic before the query is ever reached.
    click_source.push_str(
        "    produces MaybeCell(result);\n    ensures result != 0 implies value[0] == result[0];\n} by {\n    apply(lift(acquire));\n    step();\n    step(Boxed);\n    step_until(assignment(cell, 0).entry);\n    step();\n    if program::cell != 0 {\n        unfold(MaybeCell(program::cell));\n        unfold(Cell(program::cell));\n        step_until(function.exit);\n        fold(Cell(result));\n        fold(MaybeCell(result));\n        close();\n    } else {\n        unfold(MaybeCell(program::cell));\n        step_until(function.exit);\n        fold(MaybeCell(result));\n        close();\n    }\n}\n",
    );
    (c_source, click_source)
}

/// The cost contract for the composition disjunct on the store path
/// (`docs/internals/verification-efficiency.md`): stores and held owned
/// ranges grow together, and the work must not turn over into their product.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn stores_beside_many_owned_ranges_scale_near_linearly() {
    let samples = [2, 4, 8, 16]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = stores_beside_many_owned_ranges(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("acquire.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} owned-range store fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("stores beside many owned ranges", &samples);

    // Cache-only seeded runs can preserve this loaded value without querying
    // the ownership composition. The query's own scaling and checked witness
    // are pinned directly by
    // `composition_store_separation_uses_checked_aliases_without_scanning_other_owners`.
}

/// [`stores_beside_many_owned_ranges`] with the stored array held as a wide
/// range, `owns value[0..length]` for a `size_t` length: each constant-index
/// store finds its cell in a 64-bit range (`design/typed-indices.md`, step 3).
fn stores_beside_many_owned_size_t_ranges(size: usize) -> (String, String) {
    let (c_source, click_source) = stores_beside_many_owned_ranges(size);
    let c_source = c_source.replace(
        "int32* read_acquired(int32* (*acquire)(), int32* value)",
        "int32* read_acquired(int32* (*acquire)(), int32* value, unsigned long length)",
    );
    let click_source = click_source
        .replace(
            "int32* read_acquired(int32* (*acquire)(), int32* value) {",
            "int32* read_acquired(int32* (*acquire)(), int32* value, uint64 length) {",
        )
        .replace(
            &format!("    owns value[0..{size}];\n"),
            &format!("    requires {size}u64 <= length;\n    owns value[0..length];\n"),
        );
    assert!(
        c_source.contains("unsigned long length") && click_source.contains("owns value[0..length]")
    );
    (c_source, click_source)
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn stores_beside_many_owned_size_t_ranges_scale_near_linearly() {
    let samples = [2, 4, 8, 16]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = stores_beside_many_owned_size_t_ranges(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("acquire.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} owned size_t range store fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();
    assert_near_linear_scaling("stores beside many owned size_t ranges", &samples);
}

/// [`stores_beside_many_owned_size_t_ranges`] with the stored array a heap
/// block of 64-bit size: the function also owns
/// `allocation(value, length * 4u64)`, so its range is the block's wide
/// range beside its `uint64` token (`design/heap-allocation-sizes.md`, stage 3).
fn stores_beside_many_owned_64_bit_blocks(size: usize) -> (String, String) {
    let (c_source, click_source) = stores_beside_many_owned_size_t_ranges(size);
    let click_source = click_source.replace(
        "    owns value[0..length];\n",
        "    owns allocation(value, length * 4u64);\n    owns value[0..length];\n",
    );
    assert!(click_source.contains("owns allocation(value, length * 4u64)"));
    (c_source, click_source)
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn stores_beside_many_owned_64_bit_blocks_scale_near_linearly() {
    let samples = [2, 4, 8, 16]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = stores_beside_many_owned_64_bit_blocks(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("acquire.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} owned 64-bit block store fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();
    assert_near_linear_scaling("stores beside many owned 64-bit blocks", &samples);
}

/// One function that allocates a block of 64-bit size, lends it to
/// `calls` calls that each borrow and return its `uint64` token
/// (`owns allocation(p, n * 4u64)`), and frees it: every call decides the
/// token's size and the allocation's continuity.
fn calls_borrowing_a_64_bit_block(calls: usize) -> (String, String) {
    let mut c_source = String::from(
        "void *malloc(unsigned long size);\nvoid free(void *ptr);\n\nvoid keep(int *p, unsigned long n) {\n}\n\nint f(unsigned long n) {\n    int *p = malloc(n * sizeof(int));\n    if (p == 0) {\n        return 0;\n    }\n",
    );
    for _ in 0..calls {
        c_source.push_str("    keep(p, n);\n");
    }
    c_source.push_str("    free(p);\n    return 1;\n}\n");
    let click_source = String::from(
        "verifying \"keep.c\";\n\nvoid keep(int32* p, uint64 n) {\n    owns allocation(p, n * 4u64);\n    owns uninitialized(p[0..n]);\n}\n\nint32 f(uint64 n) {\n    requires 1u64 <= n and n <= 1000u64;\n    ensures result == 0 or result == 1;\n}\n",
    );
    (c_source, click_source)
}

/// The continuity of a 64-bit block across calls costs the same at each
/// call: the work grows near-linearly with the calls.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn calls_borrowing_a_64_bit_block_scale_near_linearly() {
    let samples = [2, 4, 8, 16]
        .into_iter()
        .map(|calls| {
            let (c_source, click_source) = calls_borrowing_a_64_bit_block(calls);
            let (verified, sample) = scaling_sample(calls, || {
                verify_c_sources(&click_source, &[("keep.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "{calls}-call 64-bit block fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();
    assert_near_linear_scaling("calls borrowing a 64-bit block", &samples);
}

/// The frozen byte-representation round trip
/// (`mdtests/byte_representation_roundtrip.md`) beside `unrelated` live heap
/// allocations, each null-checked with every failure path freeing the earlier
/// ones, written once, and freed at the end. `extra_copies` repeats the fixed
/// second `memcpy`.
fn roundtrip_with_unrelated_allocations(unrelated: usize, extra_copies: usize) -> String {
    let mut c = String::from(
        "void *malloc(unsigned long size);\nvoid free(void *ptr);\nvoid *memcpy(void *dest, const void *src, unsigned long n);\n\nstruct record {\n    unsigned int tag;\n    int *target;\n};\n\nint f(void) {\n",
    );
    for index in 0..unrelated {
        c.push_str(&format!(
            "    int *u{index} = malloc(sizeof(int));\n    if (u{index} == 0) {{\n"
        ));
        for previous in 0..index {
            c.push_str(&format!("        free(u{previous});\n"));
        }
        c.push_str(&format!(
            "        return -1;\n    }}\n    *u{index} = {index};\n"
        ));
    }
    let cleanup = (0..unrelated)
        .map(|index| format!("        free(u{index});\n"))
        .collect::<String>();
    c.push_str(
        &"    int *pointee = malloc(sizeof(int));
    if (pointee == 0) {
        return -1;
    }
    struct record *src = malloc(sizeof(struct record));
    if (src == 0) {
        free(pointee);
        return -1;
    }
    unsigned char *buf = malloc(16);
    if (buf == 0) {
        free(pointee);
        free(src);
        return -1;
    }
    struct record *dst = malloc(sizeof(struct record));
    if (dst == 0) {
        free(pointee);
        free(src);
        free(buf);
        return -1;
    }
    *pointee = 7;
    src->tag = 11u;
    src->target = pointee;
    memcpy(buf, (unsigned char *)(void *)src, sizeof(struct record));
    memcpy((unsigned char *)(void *)dst, buf, sizeof(struct record));
"
        .replace(
            "        return -1;\n",
            &format!("{cleanup}        return -1;\n"),
        ),
    );
    for _ in 0..extra_copies {
        c.push_str("    memcpy((unsigned char *)(void *)dst, buf, sizeof(struct record));\n");
    }
    c.push_str(
        "    int out = dst->tag + *dst->target;
    free(pointee);
    free(src);
    free(buf);
    free(dst);
",
    );
    for index in 0..unrelated {
        c.push_str(&format!("    free(u{index});\n"));
    }
    c.push_str("    return out;\n}\n");
    c
}

const ROUNDTRIP_CLICK: &str =
    "verifying \"rep_copy.c\";\n\nint f() {\n    ensures result == 18 or result == -1;\n}\n";

fn roundtrip_sample(unrelated: usize, extra_copies: usize) -> ScalingSample {
    std::thread::Builder::new()
        .name(format!("roundtrip-{unrelated}-{extra_copies}"))
        .stack_size(64 << 20)
        .spawn(move || roundtrip_sample_on_this_thread(unrelated, extra_copies))
        .expect("spawn a sample thread")
        .join()
        .expect("sample thread")
}

fn roundtrip_sample_on_this_thread(unrelated: usize, extra_copies: usize) -> ScalingSample {
    let c = roundtrip_with_unrelated_allocations(unrelated, extra_copies);
    let (verified, sample) = scaling_sample(unrelated, || {
        verify_c_sources(ROUNDTRIP_CLICK, &[("rep_copy.c", c.as_str())])
    });
    verified.unwrap_or_else(|error| {
        panic!(
            "round trip beside {unrelated} allocations with {extra_copies} extra copies failed: {}",
            error.message()
        )
    });
    sample
}

/// One extra fixed `memcpy` in the frozen byte-representation round trip
/// costs nearly the same deterministic work beside 2, 4, 8, or 16 unrelated
/// live heap allocations.
///
/// Every sample runs on its own thread after one warm-up verification, so no
/// sample pays the once-per-process standard-library setup. Measured
/// marginals on 2026-09-23: 3226, 3268, 3324, and 3468 units. They were
/// 3232, 3276, 3336, and 3488 (and 3752 at 32 allocations, too slow for a
/// debug-build unit test) while whole-function finalization still visited
/// the grouped proof's shared execution once per path theorem. Before state
/// sharing they were about 33,000 at N = 8 and 58,000 at N = 16: every later
/// free compared the copy's facts, whose embedded states were equal but
/// separately stored, entry by entry. Before resource validity read only
/// indexed candidates they were 3236, 3288, 3364, and 3548: each call's
/// ensured-resource composition swept every block the caller owned.
///
/// This guards those collapses; it is not the logarithmic contract, which
/// the expanded proof meets (see the next test). The remaining growth, about
/// 17 units per unrelated allocation, is mostly the
/// implicit tail's condition-premise search over its listed pure
/// facts and that search's solve checkpoints (about 12 per allocation); the
/// rest is re-derived state comparison relative to a base and more
/// composition separation-candidate projections. The kernel call path is
/// flat here: `ensured resource composition` and `verified call return
/// resource evaluation` charge the same work at every size.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 7s in the parallel gate"]
fn roundtrip_extra_copy_stays_nearly_flat_beside_unrelated_allocations() {
    const SIZES: [usize; 4] = [2, 4, 8, 16];
    let _ = roundtrip_sample(1, 0);
    let handles = SIZES
        .iter()
        .flat_map(|&size| [(size, 0), (size, 1)])
        .map(|(size, extra)| {
            std::thread::Builder::new()
                .name(format!("roundtrip-{size}-{extra}"))
                .stack_size(64 << 20)
                .spawn(move || roundtrip_sample_on_this_thread(size, extra).work)
                .expect("spawn a sample thread")
        })
        .collect::<Vec<_>>();
    let work = handles
        .into_iter()
        .map(|handle| handle.join().expect("sample thread"))
        .collect::<Vec<_>>();
    let marginal = work
        .chunks(2)
        .map(|pair| pair[1] as i64 - pair[0] as i64)
        .collect::<Vec<_>>();
    eprintln!("extra-copy marginal work beside {SIZES:?} allocations: {marginal:?}");
    assert!(marginal[0] > 0, "{marginal:?}");
    let allowed = marginal[0] + marginal[0] / 8;
    assert!(
        marginal.iter().all(|work| *work <= allowed),
        "one extra memcpy grew with unrelated allocations beyond {allowed}: {marginal:?}"
    );
}

/// The largest unrelated-allocation count whose expanded round trip fits the
/// checked proof drivers' nesting bound: every null check becomes one nested
/// proof `if`, and the round trip adds four of its own to the eleven allowed.
const EXPANDED_ROUNDTRIP_MAX_UNRELATED: usize = 7;

/// Expands the round trip's omitted proof beside `unrelated`
/// allocations to explicit simple tactics, outside the measurement, and
/// returns the C source length with the expanded proof's verification work.
fn expanded_roundtrip_sample(unrelated: usize, extra_copies: usize) -> (usize, ScalingSample) {
    std::thread::Builder::new()
        .name(format!("expanded-roundtrip-{unrelated}-{extra_copies}"))
        .stack_size(64 << 20)
        .spawn(move || {
            let c = roundtrip_with_unrelated_allocations(unrelated, extra_copies);
            let sources = [("rep_copy.c", c.as_str())];
            // Grouped expansion needs a written proof to replace. Check the
            // first real statement and let the implicit tail prove the rest.
            let proof = format!("{ROUNDTRIP_CLICK} by {{ step(); }}");
            let expanded =
                expand_c_claim_source(&proof, &sources, "f", ContractProofClaim::Grouped)
                    .unwrap_or_else(|error| {
                        panic!(
                            "round trip beside {unrelated} allocations with {extra_copies} extra copies should expand: {}",
                            error.message()
                        )
                    });
            assert!(!expanded.contains("execute()"), "{expanded}");
            assert!(!expanded.contains("solve()"), "{expanded}");
            let (verified, sample) =
                scaling_sample(unrelated, || verify_c_sources(&expanded, &sources));
            verified.unwrap_or_else(|error| {
                panic!(
                    "expanded round trip beside {unrelated} allocations with {extra_copies} extra copies failed: {}\n{expanded}",
                    error.message()
                )
            });
            (c.len(), sample)
        })
        .expect("spawn a sample thread")
        .join()
        .expect("sample thread")
}

/// Samples the expanded round trip at `sizes`, each with and without the
/// extra copy, every one on its own thread after one warm-up verification.
fn expanded_roundtrip_samples(sizes: &[usize]) -> Vec<[(usize, ScalingSample); 2]> {
    assert!(
        sizes
            .iter()
            .all(|size| *size <= EXPANDED_ROUNDTRIP_MAX_UNRELATED)
    );
    let _ = roundtrip_sample(1, 0);
    let handles = sizes
        .iter()
        .map(|&size| {
            [0, 1].map(|extra| {
                std::thread::Builder::new()
                    .name(format!("expanded-roundtrip-driver-{size}-{extra}"))
                    .spawn(move || expanded_roundtrip_sample(size, extra))
                    .expect("spawn a sample driver")
            })
        })
        .collect::<Vec<_>>();
    handles
        .into_iter()
        .map(|pair| pair.map(|handle| handle.join().expect("sample driver")))
        .collect()
}

/// One extra fixed `memcpy` in the frozen byte-representation round trip,
/// under its expanded proof of explicit simple tactics, costs at most a
/// logarithm more beside 1, 2, 4, or 7 unrelated live heap allocations.
/// The same samples must also have at most logarithmic whole-proof work per
/// C source byte. Keeping both assertions together avoids expanding and
/// cold-checking this identical matrix twice.
///
/// This is the contract the smart test above does not meet: both variants'
/// omitted proofs are expanded outside the measurement, and only
/// the two expanded proofs' verification is compared. Seven allocations is
/// the largest family member the checked proof drivers' nesting bound admits
/// (see [`EXPANDED_ROUNDTRIP_MAX_UNRELATED`]). Measured marginals on
/// 2026-09-23 for 1 through 7 allocations: 912, 912, 912, 912, 916, 920, and
/// 920 units. The only growth is two `SymbolicMemory::eq_relative_to` comparisons
/// at each path's end (`proof completion`, re-deriving the memory without
/// the function's local block), whose persistent-map walk deepens with the
/// heap. Before finalization visited a grouped proof's shared execution once,
/// the marginals were 917, 918, 919, 920, 925, 930, and 931, one more unit
/// per allocation: the extra copy's composition carrier was re-inserted into
/// a fresh fact context once per theorem, and a grouped proof issues one
/// theorem per path.
///
/// The whole expanded round trip costs deterministic work per C source byte
/// that grows at most logarithmically in the source beside 1, 2, 4, or 7
/// unrelated allocations.
///
/// The source is quadratic in the allocations, since every failure path
/// frees the earlier ones, and so is the checked path structure: each
/// failure path steps its own frees. Measured on 2026-09-23 for 1 through 7
/// allocations: 8449, 10068, 11842, 13779, 15885, 18154, and 20590 units over
/// 1193, 1389, 1603, 1835, 2085, 2353, and 2639 bytes, or 7.08, 7.25, 7.39,
/// 7.51, 7.62, 7.72, and 7.80 units per byte. The rise per doubling of the
/// source falls from 0.76 to 0.52 units per byte as the quadratic terms,
/// about 82 units against 9 bytes per squared allocation, take over.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 6s in the parallel gate"]
fn expanded_roundtrip_marginal_and_per_source_byte_work_are_logarithmic() {
    const SIZES: [usize; 4] = [1, 2, 4, EXPANDED_ROUNDTRIP_MAX_UNRELATED];
    let samples = expanded_roundtrip_samples(&SIZES);
    let marginal = samples
        .iter()
        .map(|[(_, without), (_, with)]| with.work as i64 - without.work as i64)
        .collect::<Vec<_>>();
    eprintln!("expanded extra-copy marginal work beside {SIZES:?} allocations: {marginal:?}");
    assert!(marginal[0] > 0, "{marginal:?}");
    let mut phase_marginals = BTreeMap::new();
    for key in samples
        .iter()
        .flat_map(|pair| pair.iter().flat_map(|(_, sample)| sample.named_work.keys()))
    {
        let values = samples
            .iter()
            .map(|[(_, without), (_, with)]| {
                with.named_work.get(key).copied().unwrap_or(0) as i64
                    - without.named_work.get(key).copied().unwrap_or(0) as i64
            })
            .collect::<Vec<_>>();
        if values.last() > values.first() {
            phase_marginals.insert(key.clone(), values);
        }
    }
    for (size, work) in SIZES.iter().zip(&marginal) {
        // Four units per doubling of the unrelated allocations; the measured
        // curve rises eight units by seven allocations, and a single unit
        // per allocation would exceed this by seven.
        let allowed = marginal[0] as f64 + 4.0 * (*size as f64 / SIZES[0] as f64).log2();
        assert!(
            *work as f64 <= allowed,
            "one extra memcpy under the expanded proof grew beyond {allowed} beside {size} allocations: {marginal:?}; growing phases: {phase_marginals:?}"
        );
    }

    // Reuse the same fully expanded, cold-checked samples for the whole-proof
    // source-byte bound as well as the extra-copy marginal above.
    let per_byte = samples
        .iter()
        .map(|[(bytes, without), _]| (*bytes, without.work, without.work as f64 / *bytes as f64))
        .collect::<Vec<_>>();
    eprintln!(
        "expanded round trip (bytes, work, work per byte) beside {SIZES:?} allocations: {per_byte:?}"
    );
    let (first_bytes, _, first_ratio) = per_byte[0];
    assert!(first_ratio > 0.0, "{per_byte:?}");
    for (size, (bytes, _, ratio)) in SIZES.iter().zip(&per_byte) {
        // One unit per byte per doubling of the source.
        let allowed = first_ratio + (*bytes as f64 / first_bytes as f64).log2();
        assert!(
            *ratio <= allowed,
            "expanded round trip work per source byte grew beyond {allowed:.3} beside {size} allocations: {per_byte:?}; named work: {}",
            named_growth_diagnostic(
                &samples
                    .iter()
                    .map(|[(_, without), _]| without.clone())
                    .collect::<Vec<_>>()
            )
        );
    }
}

/// C source with one checked allocation and `returns` early returns after it,
/// so `returns + 2` paths each carry the same few resource facts.
fn early_return_fan_out(returns: usize) -> String {
    let mut c = String::from(
        "void *malloc(unsigned long size);\nvoid free(void *ptr);\n\nint g(int a) {\n    int *p = malloc(sizeof(int));\n    if (p == 0) {\n        return -1;\n    }\n    *p = a;\n    free(p);\n",
    );
    for index in 0..returns {
        c.push_str(&format!(
            "    if (a == {index}) {{\n        return {index};\n    }}\n"
        ));
    }
    c.push_str("    return -1;\n}\n");
    c
}

/// A fixed one-store proof verified after an unrelated proof in the same
/// sidecar. Everything a proof unit builds in the session (interned states,
/// load names, memo tables) outlives it, so this is where a later proof can
/// end up walking an earlier one's history. The naming cache once returned
/// load names minted by the earlier function without refreshing their origin,
/// and the later store's pointer transport walked the earlier function's DAG
/// from that origin: 30,000 units alone became over a million, and the
/// arena's `arena_write` failed its budget only when `arena_init` ran first.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: multi-size store-history verification"]
fn a_fixed_store_proof_costs_the_same_after_a_growing_unrelated_proof() {
    const RESOURCES: &str = "resource box_state(b: struct box*) {
    field len: int32;
    owns b->data;
    owns b->len;
    owns b->data[0..len];
    fact b->len == len;
    fact 0 <= len;
    fact separate(memory(*b), memory(b->data[0..b->len]));
}

resource holder_state(h: struct holder*) {
    field start: int32;
    owns *h;
    fact h->start == start;
    fact 0 <= start;
}
";
    const FIXED_C: &str = "void one(struct holder* h, int32 i) {
    struct box* b;

    b = h->box;
    b->data[h->start + i] = 1;
}
";
    const FIXED_PROOF: &str = "void one(struct holder* h, int32 i) {
    owns r: holder_state(h);
    owns st: box_state(h->box);
    requires 0 <= i;
    requires defined(r.start + i) and r.start + i < st.len;
    ensures st.len == old(st.len);
} by {
    let { len: l } = unfold(st);
    let { start: s } = unfold(r);
    have defined(s + i) by {
        close() using {
            defined(s + i) and s + i < l;
        }
    }
    have s + i < l by {
        close() using {
            defined(s + i) and s + i < l;
        }
    }
    have s <= s + i;
    have s + i + 1 <= l by {
        close() using {
            s + i < l;
        }
    }
    have h->start == s by {
        close();
    }
    have defined(h->start + i) by {
        rewrite(h->start, s);
        close();
    }
    have h->start <= h->start + i by {
        rewrite(h->start, s);
        close();
    }
    have h->start + i + 1 <= l by {
        rewrite(h->start, s);
        close();
    }
    have 0 <= h->start + i by {
        rewrite(h->start, s);
        close() using { 0 <= s; s <= s + i; };
    }
    have h->start + i < l by {
        rewrite(h->start, s);
        close();
    }
    step_until(assignment(b, 0).entry);
    step();
    mark box_loaded;
    have b == h->box by close();
    have b->len == l by {
        rewrite(b, h->box);
        close();
    }
    have separate(memory(b->len), memory(b->data[h->start + i])) by close();
    have separate(memory(b->data), memory(b->data[h->start + i])) by close();
    have separate(memory(*b), memory(b->data[0..b->len])) by {
        rewrite(b, h->box);
        close();
    }
    step();
    have b->len == l by close();
    have b->data == at(box_loaded, b->data) by close();
    have b->len == at(box_loaded, b->len) by close();
    have separate(memory(*b), memory(b->data[0..b->len])) by {
        rewrite(b->data, at(box_loaded, b->data));
        rewrite(b->len, at(box_loaded, b->len));
        close();
    }
    let st = fold(box_state(b), { len: l });
    let r = fold(holder_state(h), { start: s });
    step_until(function.exit);
    close();
}
";
    const STRUCTS: &str = "struct box {
    int32* data;
    int32 len;
};

struct holder {
    struct box* box;
    int32 start;
};
";
    // The work of the fixed proof's own tactics, and whether it verified.
    let fixed_proof_work = |unrelated_stores: Option<usize>| {
        let (big_c, big_proof) = match unrelated_stores {
            None => (String::new(), String::new()),
            Some(stores) => (
                format!(
                    "void big(struct box* b) {{\n{}}}\n\n",
                    (0..stores)
                        .map(|index| format!("    b->data[{index}] = 0;\n"))
                        .collect::<String>()
                ),
                format!(
                    "void big(struct box* b) {{
    owns st: box_state(b);
    requires {stores} <= st.len;
    ensures st.len == old(st.len);
}} by {{
    let {{ len: l }} = unfold(st);
    {steps}
    step_until(function.exit);
    let st = fold(box_state(b), {{ len: l }});
    close();
}}

",
                    steps = (0..stores)
                        .map(|index| format!(
                            r#"
    mark store_{index};
    have separate(memory(b->len), memory(b->data[{index}])) by close();
    have separate(memory(b->data), memory(b->data[{index}])) by close();
    step();
    have b->len == l by close();
    have b->data == at(store_{index}, b->data) by close();
    have b->len == at(store_{index}, b->len) by close();
    have separate(memory(*b), memory(b->data[0..b->len])) by {{
        rewrite(b->data, at(store_{index}, b->data));
        rewrite(b->len, at(store_{index}, b->len));
        close();
    }}
"#
                        ))
                        .collect::<String>()
                ),
            ),
        };
        let c_source = format!("{STRUCTS}\n{big_c}{FIXED_C}");
        let click_source =
            format!("{RESOURCES}\nverifying \"order.c\";\n\n{big_proof}{FIXED_PROOF}");
        let (result, events) = crate::instrumentation::collect(|| {
            verify_c_sources(&click_source, &[("order.c", &c_source)])
        });
        result.unwrap_or_else(|error| {
            panic!(
                "the fixed proof after {unrelated_stores:?} unrelated stores should verify: {}",
                error.message()
            )
        });
        events
            .into_iter()
            .filter_map(|event| match event {
                crate::instrumentation::VerificationEvent::TacticFinished {
                    tactic, work, ..
                } if tactic.claim.starts_with("one.") => Some(work),
                _ => None,
            })
            .sum::<usize>()
    };
    let alone = fixed_proof_work(None);
    assert!(alone > 0);
    let samples = [4, 32].map(|stores| (stores, fixed_proof_work(Some(stores))));
    for &(stores, work) in &samples {
        // Constant plus a logarithmic allowance for indexed session tables.
        let allowance = 64 * (usize::BITS - stores.leading_zeros()) as usize;
        assert!(
            work <= alone + allowance,
            "the fixed proof's work must not depend on the unrelated proof before it: \
             alone {alone}, after (stores, work) {samples:?}"
        );
    }
}

/// A loop that marks `arena->occupied[i]` for `i` in `[start, end)` and
/// frames `cells` constant cells below `start`, one invariant per cell.
/// The back edge closes each cell's guarded member from its frame fact.
/// Logical reads do not add viewability goals or introductions to that
/// closure.
fn framed_field_cells_loop(cells: usize) -> (String, String) {
    let c_source = "struct arena {\n    int32* data;\n    int32* occupied;\n    int32 capacity;\n};\n\n\
        void mark_tail(struct arena* arena, int32 start, int32 end) {\n    int32 i;\n    i = start;\n    \
        while (i < end) {\n        arena->occupied[i] = 1;\n        i = i + 1;\n    }\n}\n"
        .to_string();
    let invariants = (0..cells)
        .map(|cell| {
            format!("        invariant arena->occupied[{cell}] == old(arena->occupied[{cell}]);\n")
        })
        .collect::<String>();
    let click_source = format!(
        "verifying \"mark_tail.c\";\n\n\
         void mark_tail(struct arena* arena, int32 start, int32 end) {{\n\
         \x20   owns *arena;\n\
         \x20   owns arena->occupied[0..arena->capacity];\n\
         \x20   requires separate(\n\
         \x20       memory(*arena),\n\
         \x20       memory(arena->occupied[0..arena->capacity])\n\
         \x20   );\n\
         \x20   requires 0 <= start;\n\
         \x20   requires {cells} <= start;\n\
         \x20   requires start <= end;\n\
         \x20   requires end <= arena->capacity;\n\
         \x20   requires end <= 1000000;\n\
         }} by {{\n\
         \x20   step();\n\
         \x20   step();\n\
         \x20   loop {{\n\
         \x20       owns arena->occupied[0..arena->capacity];\n\
         \x20       invariant start <= i;\n\
         {invariants}\
         \x20       decreases end - i;\n\
         \x20       initialize by close();\n\
         \x20       maintain by {{\n\
         \x20           have 0 <= i by {{ close(); }}\n\
         \x20           step();\n\
         \x20           step();\n\
         \x20       }}\n\
         \x20   }}\n\
         \x20   step_until(function.exit);\n\
         \x20   close();\n\
         }}\n"
    );
    (c_source, click_source)
}

/// The number of simple steps in `framed_field_cells_loop`'s explicit
/// back-edge closure: one `both` per member but the last, the members'
/// closing steps, and the preceding-clause introductions each cell makes.
fn framed_field_cells_closure_steps(cells: usize) -> usize {
    let members = 1 + cells + 2;
    let introductions = (0..cells).map(|cell| 1 + cell).sum::<usize>();
    (members - 1) + members + introductions
}

/// Framing `N` cells of a map read through a struct field costs work in
/// proportion to the explicit back-edge closure. Each cell's member is guarded
/// by every earlier clause, so the closure itself has a quadratic number of
/// introductions; the work must follow that certificate, not outgrow it.
/// Before, a later member was guarded by each earlier member whole, so the
/// bundle doubled with every declaration.
///
/// The remaining excess over the certificate is the order-fact fallback that
/// matches a condition against every stated condition fact
/// (`has_condition_fact`), which the growing set of framed-cell facts feeds.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4s in the parallel gate"]
fn framed_field_cells_back_edge_closure_follows_its_certificate() {
    let samples = [1, 4, 8]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = framed_field_cells_loop(size);
            let sources = [("mark_tail.c", c_source.as_str())];
            let (verified, sample) =
                scaling_sample(size, || verify_c_sources(&click_source, &sources));
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} framed field cells fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        let steps = framed_field_cells_closure_steps(pair[1].size) as f64
            / framed_field_cells_closure_steps(pair[0].size) as f64;
        let work = pair[1].work as f64 / pair[0].work as f64;
        assert!(
            work <= 1.5 * steps,
            "framed field cells: work grew {work:.2}x against a {steps:.2}x larger closure: \
             {samples:?}; named work: {}",
            named_growth_diagnostic(&samples),
        );
    }
}

/// A counting loop with `clauses` pure invariant declarations beside its
/// bound, closed by the back edge's smart closer.
fn many_clause_loop(clauses: usize) -> (String, String) {
    let c_source =
        "void count(int32 n) {\n    int32 i;\n    i = 0;\n    while (i < n) {\n        i = i + 1;\n    }\n}\n"
            .to_string();
    let invariants = (0..clauses)
        .map(|clause| format!("        invariant 0 - {clause} <= i;\n"))
        .collect::<String>();
    let click_source = format!(
        "verifying \"count.c\";\n\n\
         void count(int32 n) {{\n\
         \x20   requires 0 <= n;\n\
         \x20   requires n <= 1000;\n\
         \x20   ensures 0 == 0;\n\
         }} by {{\n\
         \x20   step();\n\
         \x20   step();\n\
         \x20   loop {{\n\
         \x20       invariant 0 <= i;\n\
         {invariants}\
         \x20       decreases n - i;\n\
         \x20       initialize by close();\n\
         \x20       maintain by {{\n\
         \x20           step();\n\
         \x20       }}\n\
         \x20   }}\n\
         \x20   step_until(function.exit);\n\
         \x20   close();\n\
         }}\n"
    );
    (c_source, click_source)
}

/// The back-edge bundle guards each clause by the clauses declared before
/// it, bare. Guarding by the earlier members whole doubled the bundle with
/// every declaration: sixteen clauses exhausted the smart closer's budget.
/// The guards now grow by one clause per declaration, so the bundle and the
/// closer's work stay within a quadratic curve in the declarations.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 6s in the parallel gate"]
fn many_clause_bundle_grows_at_most_quadratically() {
    let samples = [2, 4, 8, 16]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = many_clause_loop(size);
            let sources = [("count.c", c_source.as_str())];
            let (verified, sample) =
                scaling_sample(size, || verify_c_sources(&click_source, &sources));
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} many-clause fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].work <= pair[0].work.saturating_mul(9) / 2,
            "many invariant clauses: work more than quadrupled per doubling: {samples:?}; \
             named work: {}",
            named_growth_diagnostic(&samples),
        );
    }
}

/// `solve` closes a chain of equal opaque applications. Function arity stays
/// fixed so the unrelated-query axis measures ambient facts independently
/// of the cost of lowering a contract with more parameters.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn solve_equality_chain_is_linear_and_unrelated_queries_are_flat() {
    let solve_work = |sample: &ScalingSample| {
        sample
            .named_work
            .iter()
            .filter(|(name, _)| name.ends_with("tactic `solve`"))
            .map(|(_, work)| *work)
            .sum::<usize>()
    };
    let sources = |size: usize, goal: &str| {
        // Keep function arity fixed: otherwise claim lowering itself grows
        // with the parameter list, obscuring the unrelated-fact lookup axis.
        let parameters = "int32 x, int32 y, int32 z, int32 w";
        let requires = (0..size)
            .map(|index| {
                format!(
                    "    requires marker({index}, x) == marker({}, x);\n",
                    index + 1
                )
            })
            .collect::<String>();
        (
            format!("int chain({parameters}) {{\n    return 0;\n}}\n"),
            format!(
                "verifying \"chain.c\";\n\nfunction marker(index: int32, x: int32) -> int32 {{ x }}\n\nint32 chain({parameters}) {{\n{requires}    requires y == z;\n    requires z == w;\n    ensures {goal};\n}} by {{ step_until(function.exit); close(); }}\n"
            ),
        )
    };
    let mut chain = Vec::new();
    let mut unrelated = Vec::new();
    for size in [4, 8, 16, 32] {
        for (goal, samples) in [
            (format!("marker(0, x) == marker({size}, x)"), &mut chain),
            ("y == w".to_string(), &mut unrelated),
        ] {
            let (c_source, click_source) = sources(size, &goal);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("chain.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| panic!("`{goal}` closes: {}", error.message()));
            samples.push(solve_work(&sample));
        }
    }
    assert!(chain[0] > 0 && unrelated[0] > 0, "{chain:?} {unrelated:?}");
    for pair in chain.windows(2) {
        assert!(
            pair[1] <= pair[0].saturating_mul(3),
            "chain work grew faster than linear: {chain:?}"
        );
    }
    for work in &unrelated {
        assert!(
            *work <= unrelated[0].saturating_add(unrelated[0] / 4),
            "an unrelated query grew with the chain: {unrelated:?}"
        );
    }
}

/// A simplifier goal no case split can decide does not pay for case splits
/// over disjunctions about other variables: each call outcome in a long
/// proof (`result == 0 or result == 1`) used to be split, nested, before the
/// derivation failed. The split skips a disjunction sharing no variable with
/// the goal, so the failing derivation's work stays flat as they grow.
#[test]
fn failing_solve_derivation_ignores_unrelated_disjunctions() {
    use crate::kernel::{OldConditionTerm, OldMachineTerm, Proposition, PureFactContext, Variable};

    let equal = |variable: u64, value: u32| {
        Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(OldMachineTerm::Variable(Variable(variable))),
                right: Box::new(OldMachineTerm::constant(value)),
            },
            true,
        )
    };
    let samples = [2, 4, 6, 8]
        .into_iter()
        .map(|size| {
            let mut context = PureFactContext::new();
            for index in 0..size {
                let variable = 432_000 + index as u64;
                context = context.assume_proposition(Proposition::Or(
                    Box::new(equal(variable, 0)),
                    Box::new(equal(variable, 1)),
                ));
            }
            let goal = Proposition::condition_is(
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: Box::new(OldMachineTerm::Variable(Variable(433_000))),
                    right: Box::new(OldMachineTerm::constant(5)),
                },
                true,
            );
            let (derivation, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::search::ProofSearch::derive_solve_proposition(&(context), &goal)
            });
            assert!(derivation.is_none(), "nothing bounds the goal's variable");
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(64),
            "unrelated disjunctions were split: {samples:?}"
        );
    }
}

/// The same holds for a disjunction over no machine variable, such as a
/// model's constructor cases (`c == Color::Red or c == Color::Black`): one
/// whose variables the goal does not name is not split under it either.
#[test]
fn failing_solve_derivation_ignores_unrelated_algebraic_disjunctions() {
    use crate::kernel::{
        AlgebraicSchemas, AlgebraicTerm, AlgebraicTermNode, AlgebraicType, AlgebraicValueType,
        AlgebraicVariantType, OldConditionTerm, OldMachineTerm, Proposition, PureFactContext, Term,
        Variable,
    };

    let variants: std::sync::Arc<[AlgebraicVariantType]> = ["Red", "Black"]
        .into_iter()
        .map(|name| AlgebraicVariantType {
            name: name.into(),
            fields: vec![],
        })
        .collect::<Vec<_>>()
        .into();
    let color = AlgebraicType {
        rigid: false,
        name: "Color".into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            AlgebraicValueType::Algebraic {
                name: "Color".into(),
                arguments: vec![],
            },
            variants,
        )]))),
    };
    let term = |node| {
        Term::Algebraic(
            AlgebraicTerm {
                algebraic_type: color.clone(),
                node,
            }
            .into(),
        )
    };
    let is = |variable: u64, variant: &str| {
        Proposition::Equal(
            term(AlgebraicTermNode::Variable(Variable(variable))),
            term(AlgebraicTermNode::Constructor {
                variant: variant.into(),
                fields: vec![],
            }),
        )
    };
    let samples = [2, 4, 6, 8]
        .into_iter()
        .map(|size| {
            let mut context = PureFactContext::new();
            for index in 0..size {
                let variable = 434_000 + index as u64;
                context = context.assume_proposition(Proposition::Or(
                    Box::new(is(variable, "Red")),
                    Box::new(is(variable, "Black")),
                ));
            }
            let goal = Proposition::condition_is(
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: Box::new(OldMachineTerm::Variable(Variable(435_000))),
                    right: Box::new(OldMachineTerm::constant(5)),
                },
                true,
            );
            let (derivation, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::search::ProofSearch::derive_solve_proposition(&(context), &goal)
            });
            assert!(derivation.is_none(), "nothing bounds the goal's variable");
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(64),
            "unrelated algebraic disjunctions were split: {samples:?}"
        );
    }
}

fn branching_grouped_claim_project(claim_count: usize) -> (String, String) {
    let c_source = "int32 branching_claims(int32 a) {\n    int32 x;\n    if (a == 0) {\n        return 0;\n    }\n    x = a;\n    return x;\n}\n"
        .to_string();
    let mut click_source = String::from(
        "verifying \"branching_claims.c\";\n\nint32 branching_claims(int32 a) {\n    requires 0 <= a;\n    requires a <= 10;\n",
    );
    for _ in 0..claim_count {
        click_source.push_str("    ensures result == a;\n");
    }
    click_source.push_str(
        "} by {\n    step();\n    branch { true => {\n            step_until(function.exit);\n            close();\n        } false => {} }\n    step();\n    have x == a by {\n        close();\n    }\n    step_until(function.exit);\n    close();\n}\n",
    );
    (c_source, click_source)
}

/// A grouped proof issues one theorem per path and claim. Each used to carry
/// its own copy of the function block, which holds the whole grouped proof,
/// and of the proof's tactics, and finishing compared every new theorem with
/// every earlier one field by field, so finishing cost the proof's size times
/// the number of theorems (twice that number squared for the comparisons).
/// None of that is deterministic work, so the curve alone cannot see it: the
/// theorems must share one proof text at every size.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn grouped_proof_theorems_share_one_proof_text() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = branching_grouped_claim_project(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("branching_claims.c", c_source.as_str())])
            });
            let verified = verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} branching grouped-claim fixture failed: {}",
                    error.message()
                )
            });
            assert!(
                verified.len() >= size,
                "size {size}: every claim should be issued: {} theorems",
                verified.len()
            );
            let first = &verified[0];
            let first_tactics = first
                .proof_tactics
                .as_ref()
                .expect("a grouped script theorem retains its proof tactics");
            let first_expanded = first.expanded_proof.as_ref().expect("grouped expansion");
            for theorem in &verified {
                assert!(
                    theorem
                        .expanded_proof
                        .as_ref()
                        .is_some_and(|certificate| certificate.shares_steps_with(first_expanded)),
                    "size {size}: grouped claims copied their shared expansion"
                );
                assert!(
                    std::sync::Arc::ptr_eq(&theorem.function_block, &first.function_block),
                    "size {size}: a theorem carries its own copy of the function block"
                );
                assert!(
                    theorem
                        .proof_tactics
                        .as_ref()
                        .is_some_and(|tactics| std::sync::Arc::ptr_eq(tactics, first_tactics)),
                    "size {size}: a theorem carries its own copy of the proof tactics"
                );
            }
            sample
        })
        .collect::<Vec<_>>();
    assert_near_linear_scaling("theorems of one branching grouped proof", &samples);
}

/// One project whose caller makes `call_count` plain `step()`s over a callee
/// that advances one counter field of an owned object and keeps its other
/// field. Every call's equality ensures name a load at the previous call's
/// state, so the counter's constant after normalization runs through the
/// whole prior call chain -- the `arena_free` shape (`after.live ==
/// old(st.live) - 1`, `region->start == old(r.start)`).
fn counter_call_chain(call_count: usize) -> (String, String) {
    let mut c_source = String::from(
        "struct range {\n    int32 start;\n    int32 end;\n};\n\nvoid touch(struct range* r) {\n    r->end = r->end + 1;\n}\n\nvoid drive(struct range* r) {\n",
    );
    for _ in 0..call_count {
        c_source.push_str("    touch(r);\n");
    }
    c_source.push_str("}\n");
    let mut click_source = String::from(
        "verifying \"drive.c\";\n\nvoid touch(struct range* r) {\n    owns *r;\n    requires r->end < 1000000;\n    ensures r->end == old(r->end) + 1;\n    ensures r->start == old(r->start);\n}\n\n",
    );
    click_source.push_str(&format!(
        "void drive(struct range* r) {{\n    owns *r;\n    requires r->end == 0;\n    ensures r->end == {call_count};\n}} by {{\n"
    ));
    for previous in 0..call_count {
        // Check the call against the end value established by the preceding
        // ensure (or the caller's entry fact for the first call).
        click_source.push_str(&format!(
            "    step() {{\n        requires r->end < 1000000 by close() using {{ r->end == {previous}; }};\n        requires aligned(r, 4) by close();\n    }}\n"
        ));
    }
    click_source.push_str("    step_until(function.exit);\n    close();\n}\n");
    (c_source, click_source)
}

/// A simple `step()` over a call lowers the callee's equality ensures in work
/// proportional to that call, not to the caller's prior call chain.
///
/// Normalizing an ensured term to its constant used to re-walk every earlier
/// call's ensures, deep-comparing each same-address load at another state:
/// the Nth call cost O(N^2) and the proof O(N^3). The constant is now a class
/// lookup maintained as each fact is inserted, so the last call's lowering is
/// flat in N and the whole proof is near-linear.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 12s in the parallel gate"]
fn counter_call_chain_ensure_lowering_stays_flat_per_call() {
    const LOWERING: &str = "verified call provisional ensure lowering";
    let mut last_lowering = Vec::new();
    let mut totals = Vec::new();
    for size in [1, 2, 4, 8] {
        let (c_source, click_source) = counter_call_chain(size);
        let ((verified, work), events) = crate::instrumentation::collect(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                verify_c_sources(&click_source, &[("drive.c", c_source.as_str())])
            })
        });
        verified.unwrap_or_else(|error| {
            panic!("size {size} counter call chain failed: {}", error.message())
        });
        let lowerings = events
            .iter()
            .filter_map(|event| match event {
                crate::instrumentation::VerificationEvent::OperationFinished {
                    function,
                    name,
                    work,
                    ..
                } if name == LOWERING && function == "touch" => Some(*work),
                _ => None,
            })
            .collect::<Vec<_>>();
        // Verification lowers each call's ensures once in execution order;
        // certificate checking lowers them again, so read the costliest call
        // rather than a position.
        assert!(
            lowerings.len() >= size,
            "every call must lower its ensures: {lowerings:?}"
        );
        last_lowering.push((size, lowerings.iter().copied().max().unwrap()));
        totals.push(ScalingSample {
            size,
            work,
            named_work: BTreeMap::new(),
        });
    }
    let (_, smallest) = last_lowering[0];
    let (_, largest) = *last_lowering.last().unwrap();
    // Constant plus a logarithmic index factor: eight times the calls may
    // not even double the costliest call's lowering.
    assert!(
        largest <= smallest.max(1) * 2,
        "a call's ensure lowering must not grow with the prior call chain: {last_lowering:?}"
    );
    // At the largest sample the synthetic pair scan below adds 28 units.
    // Keep the indexing slack below that so the negative control can fail.
    let indexed = |costs: &[(usize, usize)]| costs.iter().all(|(_, work)| *work <= costs[0].1 + 16);
    eprintln!("counter-call ensure lowering: {last_lowering:?}");
    assert!(indexed(&last_lowering), "{last_lowering:?}");
    let rescanned = last_lowering
        .iter()
        .map(|(size, work)| (*size, work + size * (size - 1) / 2))
        .collect::<Vec<_>>();
    assert!(
        !indexed(&rescanned),
        "the smaller fixture must detect a quadratic call lowering: {last_lowering:?}"
    );
    assert_near_linear_scaling_with_increment_bound("counter call chain", &totals);
}

/// The callee sees one by-value argument, even when the caller has built
/// a long arithmetic expression for that value before the call.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.1s in the parallel gate"]
fn call_preparation_and_ensures_keep_the_computed_argument_shared() {
    use crate::instrumentation::VerificationEvent;

    const PREPARATION: &str = "verified call argument preparation";
    const LOWERING: &str = "verified call ensure lowering";
    let mut samples = Vec::new();
    for (depth, unrelated) in [(4, 0), (16, 0), (48, 0), (4, 32)] {
        let unrelated_locals = (0..unrelated)
            .map(|index| format!("    uint32 local{index} = x;\n"))
            .collect::<String>();
        let updates = "    x = x * 3u + 1u;\n".repeat(depth);
        let steps = "    step();\n".repeat(depth + 2 * unrelated);
        let c = format!(
            "extern uint32 echo(uint32 value);\nuint32 caller(uint32 x) {{\n{unrelated_locals}{updates}    return echo(x);\n}}"
        );
        let postcondition = format!("r == at(statement({}).entry, x)", depth + unrelated);
        let click = format!(
            "verifying \"echo.c\";\n\
             extern uint32 echo(uint32 value) {{ ensures result == old(value); }}\n\
             uint32 caller(uint32 x) {{ ensures result == result; }} by {{\n{steps}\
             let {{ result: r }} = step(echo, {{ }});\n\
             have {postcondition} by {{ close(); }}\n\
             step();\n}}"
        );
        let sources = [("echo.c", c.as_str())];
        let (verified, events) =
            crate::instrumentation::collect(|| verify_c_sources(&click, &sources));
        verified.unwrap_or_else(|error| {
            panic!("depth {depth}, unrelated {unrelated}: {}", error.report())
        });

        let mut preparation = None;
        let mut lowering = None;
        for event in events {
            if let VerificationEvent::OperationFinished {
                function,
                name,
                work,
                ..
            } = event
                && function == "echo"
            {
                match name.as_str() {
                    PREPARATION => preparation = Some(preparation.unwrap_or(0).max(work)),
                    LOWERING => lowering = Some(lowering.unwrap_or(0).max(work)),
                    "verified call provisional ensure lowering" => {
                        panic!("a resource-free call does not need provisional ensures")
                    }
                    _ => {}
                }
            }
        }
        samples.push((
            preparation.expect("the call's argument was prepared"),
            lowering.expect("the call's ensure was lowered"),
        ));

        if depth == 48 {
            let wrong = click.replace(&postcondition, "r == old(x)");
            assert!(verify_c_sources(&wrong, &sources).is_err());
        }
    }
    assert!(
        samples.iter().all(|&(preparation, lowering)| {
            preparation <= samples[0].0 + 16 && lowering <= samples[0].1 + 32
        }),
        "call argument preparation or ensure lowering grew with argument depth or unrelated locals: {samples:?}"
    );
}

/// The first call can register a previously unseen expression. Later statement
/// publications must use the same graph when they add another result equality.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn repeated_call_publication_reuses_the_argument_registration() {
    use crate::instrumentation::VerificationEvent;

    let mut samples = Vec::new();
    for depth in [8, 32, 64] {
        let updates = "    x = x * 3u + 1u;\n".repeat(depth);
        let steps = "    step();\n".repeat(depth);
        let c = format!(
            "extern uint32 echo(uint32 value);\nvoid caller(uint32 x) {{\n{updates}    echo(x);\n    echo(x);\n}}"
        );
        let click = format!(
            "verifying \"echo.c\";\n\
             extern uint32 echo(uint32 value) {{ ensures result == old(value); }}\n\
             void caller(uint32 x) {{ ensures true; }} by {{\n{steps}    step();\n    step();\n}}"
        );
        let (verified, events) =
            crate::instrumentation::collect(|| verify_c_sources(&click, &[("echo.c", &c)]));
        verified.unwrap_or_else(|error| panic!("depth {depth}: {}", error.report()));
        let work = events.iter().find_map(|event| match event {
            VerificationEvent::TacticFinished { tactic, work, .. }
                if tactic.tactic_name == "step" && tactic.source_index == depth + 1 =>
            {
                Some(*work)
            }
            _ => None,
        });
        samples.push(work.expect("the second call was stepped"));
    }
    assert!(
        samples.iter().all(|&work| work <= samples[0] + 64),
        "publishing a new equality rewalked the argument: {samples:?}"
    );
}

/// The return paths share the kernel's indexed effects for the common prefix.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn returning_branches_share_the_checked_effect_context() {
    for stores in [8, 32, 64] {
        let writes = (1..=stores)
            .map(|value| format!("    p[0] = {value}u;\n"))
            .collect::<String>();
        let steps = "    step();\n".repeat(stores);
        let c = format!(
            "uint32 caller(uint32* p, uint32 x) {{\n{writes}\
             if (x <= 2u) {{ if (x == 1u) return 1u; else return 2u; }}\n\
             else {{ if (x == 3u) return 3u; else return 4u; }} }}"
        );
        let click = format!(
            "verifying \"returns.c\";\n\
             uint32 caller(uint32* p, uint32 x) {{ owns *p; ensures result <= 4; }} by {{\n{steps}\
                 branch {{\n\
                   true => {{ branch {{ true => {{ step(); close(); }} false => {{ step(); close(); }} }} }}\n\
                   false => {{ branch {{ true => {{ step(); close(); }} false => {{ step(); close(); }} }} }}\n\
                 }}\n}}"
        );
        use crate::kernel::proof::ExecutionProofCore;
        ExecutionProofCore::take_checked_path_effect_admissions();
        crate::surface::proof::take_outcome_fact_reads();
        verify_c_sources(&click, &[("returns.c", c.as_str())])
            .unwrap_or_else(|error| panic!("{stores} writes: {}", error.report()));
        let (reused, imported) = crate::surface::proof::take_outcome_fact_reads();
        assert!(
            reused >= 4,
            "{stores} writes: reused {reused} outcome contexts"
        );
        assert_eq!(imported, 0, "{stores} writes: replayed shared effects");
        let admitted = ExecutionProofCore::take_checked_path_effect_admissions();
        assert!(
            (stores..=stores + 8).contains(&admitted),
            "{stores} writes: indexed {admitted} path effects"
        );
    }
}

/// One `step()` over a call whose external contract has `N` ensures lowers
/// them in work linear in `N`.
///
/// Each ensure is lowered under the call's context plus every fact already
/// published, and that context used to be rebuilt from the whole growing
/// fact list for every ensure: quadratic wall time (0.05 s, 0.23 s, 0.92 s
/// at 100, 200, 400 ensures; 25 s at 1,000) while the counter, which does not
/// charge a context rebuild, reported linear work. The context is now
/// extended by each ensure's own facts. The test pins both the charged
/// lowering work and the entries the verification's context rebuilds assume
/// (`context_rebuild_entries`), which a return of the per-ensure rebuild
/// makes quadratic.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn call_ensure_lowering_is_linear_in_the_ensure_count() {
    const SPANS: [&str; 2] = [
        "operation `verified call provisional ensure lowering`",
        "operation `verified call ensure lowering`",
    ];
    let mut samples = Vec::new();
    let mut lowering = Vec::new();
    let mut rebuilds = Vec::new();
    for size in [16, 32, 64, 128] {
        let ensures = (1..=size)
            .map(|k| format!("    ensures result != {k};\n"))
            .collect::<String>();
        let click_source = format!(
            "verifying \"many_ensures.c\";\n\n\
             extern int32 g(int32 x) {{\n{ensures}}}\n\n\
             int32 caller(int32 x) {{\n    ensures result != 1;\n}} by {{\n    \
             step();\n    step();\n    close();\n}}\n"
        );
        let rebuilds_before = crate::kernel::reasoning::path_facts::context_rebuild_entries();
        let (verified, sample) = scaling_sample(size, || {
            verify_c_sources(
                &click_source,
                &[(
                    "many_ensures.c",
                    "int32 g(int32 x);\n\nint32 caller(int32 x) {\n    return g(x);\n}\n",
                )],
            )
        });
        rebuilds.push(
            crate::kernel::reasoning::path_facts::context_rebuild_entries() - rebuilds_before,
        );
        verified.unwrap_or_else(|error| {
            panic!("size {size} many-ensures call failed: {}", error.message())
        });
        lowering.push(
            SPANS
                .iter()
                .map(|span| sample.named_work.get(*span).copied().unwrap_or(0))
                .sum::<usize>(),
        );
        samples.push(sample);
    }
    assert!(
        lowering[0] > 0,
        "the ensures were never lowered: {lowering:?}"
    );
    // Linear with a small allowance: each doubling of the ensures at most
    // 2.2 times the lowering work (a quadratic rebuild is 4 times).
    for pair in lowering.windows(2) {
        assert!(
            pair[1] * 10 <= pair[0] * 22,
            "call ensure lowering grows faster than the ensure count: {lowering:?}"
        );
    }
    for pair in rebuilds.windows(2) {
        assert!(
            pair[1] * 10 <= pair[0] * 22,
            "the call's context rebuilds grow faster than the ensure count: {rebuilds:?}"
        );
    }
    // At half the former maximum M, 28/13 on increments rejects
    // a > 2*k/(9*M) in B + k*N + a*N^2: the former 2.2x
    // whole-work crossover, without slack from fixed setup.
    assert_bounded_work_increments("call ensure count: selected work", &lowering, 28, 13);
    assert_bounded_work_increments("call ensure count: context rebuilds", &rebuilds, 28, 13);
    assert_near_linear_scaling_with_increment_bound("call ensure count", &samples);
}

/// One `step()` over a call whose external contract has `N` requirements,
/// each discharged by the caller's one order fact, checks them in work
/// linear in `N`.
///
/// Three costs grew with the requirements already checked: the requirement
/// context was rebuilt from every earlier requirement per requirement, the
/// memory-resolution fact match scanned every condition fact of that growing
/// context, and each new context's order facts were collected by scanning
/// every condition fact. The counter reported 10.5k, 38.5k, and 147k units
/// at 50, 100, and 200 requirements. The context is now extended, the match
/// reads the condition-match index, and the order facts are an index of
/// their own.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn call_requirement_checking_is_linear_in_the_requirement_count() {
    const SPAN: &str = "operation `verified call requirement checking`";
    let mut samples = Vec::new();
    let mut checking = Vec::new();
    let mut rebuilds = Vec::new();
    for size in [8, 16, 32, 64] {
        let requires = (1..=size)
            .map(|k| format!("    requires x != {k};\n"))
            .collect::<String>();
        // Establish each requirement at the frontier from the same bound.
        // This measures checking the call's requirements at every size.
        let evidence = (1..=size)
            .map(|k| format!("    have x != {k} by close() using {{ x > {size}; }};\n"))
            .collect::<String>();
        let click_source = format!(
            "verifying \"many_requires.c\";\n\n\
             extern int32 g(int32 x) {{\n{requires}    ensures result == x;\n}}\n\n\
             int32 caller(int32 x) {{\n    requires x > {size};\n    ensures result == x;\n}} by {{\n\
             {evidence}    step();\n    step();\n    close();\n}}\n"
        );
        let rebuilds_before = crate::kernel::reasoning::path_facts::context_rebuild_entries();
        let (verified, sample) = scaling_sample(size, || {
            verify_c_sources(
                &click_source,
                &[(
                    "many_requires.c",
                    "int32 g(int32 x);\n\nint32 caller(int32 x) {\n    return g(x);\n}\n",
                )],
            )
        });
        verified.unwrap_or_else(|error| {
            panic!("size {size} many-requires call failed: {}", error.message())
        });
        rebuilds.push(
            crate::kernel::reasoning::path_facts::context_rebuild_entries() - rebuilds_before,
        );
        checking.push(sample.named_work.get(SPAN).copied().unwrap_or(0));
        samples.push(sample);
    }
    assert!(
        checking[0] > 0,
        "the requirements were never checked: {checking:?}"
    );
    // Linear with a small allowance: each doubling of the requirements at
    // most 2.2 times the checking work (the quadratic was nearly 4 times).
    for pair in checking.windows(2) {
        assert!(
            pair[1] * 10 <= pair[0] * 22,
            "call requirement checking grows faster than the requirement count: {checking:?}"
        );
    }
    for pair in rebuilds.windows(2) {
        assert!(
            pair[1] * 10 <= pair[0] * 22,
            "the call's context rebuilds grow faster than the requirement count: {rebuilds:?}"
        );
    }
    // At half the former maximum M, 28/13 on increments rejects
    // a > 2*k/(9*M) in B + k*N + a*N^2: the former 2.2x
    // whole-work crossover, without slack from fixed setup.
    assert_bounded_work_increments("call requirement count: selected work", &checking, 28, 13);
    assert_bounded_work_increments(
        "call requirement count: context rebuilds",
        &rebuilds,
        28,
        13,
    );
    assert_near_linear_scaling_with_increment_bound("call requirement count", &samples);
}

/// A call's separation requirements cost the same work beside 2, 4, 8 and
/// 16 unrelated owned objects. Every object a pointer parameter reaches
/// shares one block, so the composition-law route used to ask every owned
/// member of that block whether it held each side. The null-guarded shape
/// of `examples/rbtree/rbtree-augmented`'s `sized_rotate`, `p == 0 or
/// separate(memory(p), memory(p->f))` with `p == 0` known, also asked its
/// right disjunct, a separation nothing can establish, which every route
/// then refused only after visiting the whole frame. Measured on
/// 2026-10-15 before the fix, release build: 1,037, 1,857, 3,497 and 6,777
/// units of requirement checking for the separated call, and 9,454,
/// 15,914, 28,834 and 54,674 for the guarded requirements beyond the cost
/// of the bare guard; after it, 46 and 171 at every size.
///
/// The bare guard `a->left == 0` is measured on its own and subtracted: its
/// first lookup keys the caller's stated facts, one per owned field, into
/// the context's deferred stated index, which each fact pays once
/// (`docs/internals/verification-efficiency.md`, "Representation
/// requirements"). A separation the caller cannot show is still refused.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 13.9s in the parallel gate"]
fn call_separation_requirements_ignore_unrelated_owned_objects() {
    const SPAN: &str = "operation `verified call requirement checking`";
    let separated = "requires separate(memory(a->left), memory(b->size));";
    let guard = "requires a->left == 0;";
    let guarded = "requires a->left == 0 or separate(memory(a->left), memory(a->left->size));\n    \
                   requires separate(memory(a->left), memory(b->size));";
    let unproved = "requires separate(memory(a->left), memory(b->left));";
    let mut separated_work = Vec::new();
    let mut guarded_work = Vec::new();
    let mut refused_work = Vec::new();
    // Exact selected-work equality retains its original endpoint comparison.
    for size in [2, 16] {
        let parameters = (0..size)
            .map(|i| format!(", struct node* q{i}"))
            .collect::<String>();
        let owners = (0..size)
            .map(|i| format!("    owns q{i}->left;\n    owns q{i}->size;\n"))
            .collect::<String>();
        let c_source = format!(
            "struct node {{ struct node* left; struct node* right; int32 size; }};\n\
             void callee(struct node* a, struct node* b);\n\
             void caller(struct node* a, struct node* b{parameters}) {{ callee(a, b); }}\n"
        );
        let checking = |requirement: &str, caller_requirement: &str| {
            let click_source = format!(
                "verifying \"owners.c\";\n\
                 extern void callee(struct node* a, struct node* b) {{\n    \
                 views a->left;\n    owns b->size;\n    {requirement}\n}}\n\
                 void caller(struct node* a, struct node* b{parameters}) {{\n    \
                 owns a->left;\n    owns b->size;\n    {caller_requirement}\n{owners}\
                 }} by {{\n    step();\n    step();\n}}\n"
            );
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("owners.c", &c_source)])
            });
            (verified, sample.named_work.get(SPAN).copied().unwrap_or(0))
        };
        let run = |requirement: &str, caller_requirement: &str| {
            let (verified, work) = checking(requirement, caller_requirement);
            verified.unwrap_or_else(|error| {
                panic!(
                    "`{requirement}` beside {size} owned objects: {}",
                    error.message()
                )
            });
            assert!(work > 0, "`{requirement}` was never checked");
            work
        };
        separated_work.push(run(separated, ""));
        guarded_work.push(run(guarded, guard) - run(guard, guard));
        // `b->left` is neither owned nor separated from `a->left` by
        // anything the caller knows: the requirement stays unproved.
        let (refused, work) = checking(unproved, "");
        refused_work.push(work);
        assert!(
            refused.is_err(),
            "an unestablished separation passed beside {size} owned objects"
        );
    }
    eprintln!(
        "call separation work: proved {separated_work:?}, guarded {guarded_work:?}, refused {refused_work:?}"
    );
    assert!(
        refused_work
            .iter()
            .all(|work| *work > 0 && *work == refused_work[0]),
        "refused requirement checking grows with unrelated owners: {refused_work:?}"
    );
    assert!(
        separated_work.iter().all(|work| *work == separated_work[0]),
        "separation requirement checking grows with unrelated owned objects: {separated_work:?}"
    );
    assert!(
        guarded_work.iter().all(|work| *work == guarded_work[0]),
        "null-guarded requirement checking grows with unrelated owned objects: {guarded_work:?}"
    );
}

/// Collecting the variables of a state's memory reads the state's counts,
/// kept once per session from its derivation base's, so a proof beside a
/// global array visits each of the array's cells once however many steps
/// collect the state's variables. Walking the live memory whole on every
/// collection visited them eight times for a one-statement body and 22 for
/// an eight-statement one (2020 and 5562 visits beside 250 elements, 8020
/// and 22062 beside 1000); a global array of 100000 elements exhausted the
/// wall-clock limit.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn collecting_a_states_variables_visits_a_global_array_once() {
    let c_source = |length: u64, statements: usize| {
        format!(
            "int32 g[{length}];\n\nint32 inc(int32 x) {{\n    int32 y = x;\n{}    return y;\n}}\n",
            "    y = y + 1;\n".repeat(statements)
        )
    };
    let click_source = |statements: usize| {
        format!(
            "verifying \"inc.c\";\n\nint32 inc(int32 x) {{\n    requires x < 100;\n    ensures to_integer(result) == to_integer(x + {statements});\n}}\n"
        )
    };
    let samples = [
        (250u64, 1usize),
        (250, 8),
        (500, 1),
        (500, 8),
        (1_000, 1),
        (1_000, 8),
    ]
    .map(|(length, statements)| {
        let (verified, visits) = crate::kernel::count_cells_collected(|| {
            verify_c_sources(
                &click_source(statements),
                &[("inc.c", &c_source(length, statements))],
            )
        });
        verified.unwrap_or_else(|error| {
            panic!(
                "a body of {statements} statements beside a global array of {length} \
                     elements should verify: {}",
                error.message()
            )
        });
        (length, statements, visits)
    });
    for (length, statements, visits) in samples {
        let length = usize::try_from(length).expect("small length");
        assert!(
            visits <= length + 4 * statements + 16,
            "collection visits each element of the global array at most once: {samples:?}"
        );
    }
    for pair in samples.chunks(2) {
        let [(_, _, short), (_, _, long)] = pair else {
            unreachable!("samples come in pairs");
        };
        assert!(
            long - short <= 64,
            "more statements must not revisit the array: {samples:?}"
        );
    }
}

/// A constant range is one run of seeded cells, so a proof over it costs the
/// same whatever the range's length. Before runs, every element was a stored
/// cell and each load scanned all of them: `views a[0..100000]` exhausted
/// the simple-tactic budget, and `views a[0..1000000]` minted enough load
/// identities to collide.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn a_constant_view_costs_the_same_whatever_its_length() {
    let c_source = "int32 get(int32 *a, int32 i) { return a[i]; }\n";
    let click_source = |length: u64| {
        format!(
            "verifying \"get.c\";\n\nint32 get(int32 *a, int32 i) {{\n    views a[0..{length}];\n    requires 0 <= i;\n    requires i < {length};\n    ensures result == a[i];\n}}\n"
        )
    };
    // One unmeasured verification first: what the first verification on a
    // thread pays once (parsing the prelude, filling shared caches) is not
    // a cost of the range.
    verify_c_sources(&click_source(8), &[("get.c", c_source)]).expect("warm-up verifies");
    let samples = [8u64, 1_000, 1_000_000, 1_000_000_000].map(|length| {
        let measure = || {
            let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c_sources(&click_source(length), &[("get.c", c_source)])
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "a view of {length} elements should verify: {}",
                    error.message()
                )
            });
            work
        };
        let work = measure();
        // The work is the build profile's too: a debug build's self-checks
        // (at most `CHECKED_RUN_SLOTS` slots, so only the short views) must
        // not leave a later charged read cheaper than a release build finds
        // it. A length-8 view once cost 1796 in release and 1718 in debug:
        // contract entry named every element of a view of at most 64 to ask
        // whether each was loadable, and in debug a check had already named
        // them uncharged.
        let release_work = crate::instrumentation::without_debug_checks(measure);
        assert_eq!(
            work, release_work,
            "a view of {length} elements costs {work} with debug checks and {release_work} without"
        );
        (length, work)
    });
    let least = samples
        .iter()
        .map(|(_, work)| *work)
        .min()
        .expect("samples");
    let most = samples
        .iter()
        .map(|(_, work)| *work)
        .max()
        .expect("samples");
    assert!(least > 0, "{samples:?}");
    // Flat, not merely sublinear: the samples may differ by a few units of
    // fixed work, and the bound only has to rule out any growth with the
    // length.
    assert!(
        most - least <= 4,
        "deterministic work depends on the range's length: {samples:?}"
    );
}

/// A back-edge closure whose quantified invariant is not restated
/// at the back edge closes it from the loop head's own universal, not by
/// whole-bundle simplification. `search_terminates_by_unmarked_count.md`
/// transports the quantified `next` bound explicitly before closing; the
/// same proof without that transport must cost a small multiple of it.
/// Before the direct member pass, the variant's two closes spent about 300k
/// units (whole-bundle simplification failed, then the member planner
/// succeeded) against about 19k for the explicit proof.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4s in the parallel gate"]
fn the_back_edge_without_the_explicit_transport_costs_a_small_multiple() {
    let markdown = include_str!("../../../../mdtests/search_terminates_by_unmarked_count.md");
    let mdtest = crate::cli::parse_mdtest(
        std::path::Path::new("search_terminates_by_unmarked_count.md"),
        markdown,
    )
    .unwrap();
    let explicit = mdtest.click_source.as_deref().unwrap().replace(
        "import \"unmarked_count_lemmas.click\";",
        include_str!("../../../../mdtests/unmarked_count_lemmas.click"),
    );
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let transport = "            have forall (k: int32) {\n                0 <= k and k < n implies 0 <= next[k] and next[k] < n\n            } by {\n                transport(";
    let start = explicit
        .find(transport)
        .expect("the fixture transports the quantified bound explicitly");
    let end = start
        + explicit[start..]
            .find("            transport(\n                forall (k: int32) { 0 <= k and k < n implies at(iter, next[k]) == at(iter, next[k]) },")
            .expect("the next explicit proof step follows the transport");
    let implicit = format!("{}{}", &explicit[..start], &explicit[end..]);
    let measure = |source: &str| {
        let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
            verify_c_sources(source, &c_sources)
        });
        verified.unwrap_or_else(|error| panic!("{}", error.message()));
        work
    };
    // The first verification on a thread fills shared caches once.
    measure(&explicit);
    let explicit_work = measure(&explicit);
    let implicit_work = measure(&implicit);
    assert!(
        implicit_work <= explicit_work.saturating_mul(3) / 2,
        "closing without the explicit transport costs {implicit_work} units against {explicit_work}"
    );
}

/// A function whose contract views `size` arrays over one shared length and
/// owns one more, with a body that touches none of them.
fn many_viewed_arrays(size: usize, owned: bool) -> (String, String) {
    let params = (0..size)
        .map(|index| format!("int32 *a{index}"))
        .chain(owned.then(|| "int32 *out".to_string()))
        .chain(std::iter::once("int32 n".to_string()))
        .collect::<Vec<_>>()
        .join(", ");
    let c_source = format!("int32 f({params}) {{\n    return n;\n}}\n");
    let mut click_source = format!("verifying \"f.c\";\nint32 f({params}) {{\n");
    for index in 0..size {
        click_source.push_str(&format!("    views a{index}[0..n];\n"));
    }
    if owned {
        click_source.push_str("    owns out[0..1];\n");
    }
    click_source.push_str("    ensures result == n;\n}\n");
    (c_source, click_source)
}

/// The entry of a contract with `N` views beside one owner
/// (`docs/internals/verification-efficiency.md`). The entry partition states
/// `N` owner/view separations, and each of the `N` derived `viewable` facts
/// looks for a held range covering it. That lookup used to ask every held
/// range of the parameters' shared block, and each asked the
/// explicit-separation veto first, which walks every separation: `N^3` at
/// entry (1,542,282 units at `N = 32`, against 140,617 now).
///
/// The veto's curve is pinned near-linear: it is now asked only of a pair
/// another route covers. Each `viewable` fact a proof starts from is one the
/// contract entry states outright, so no coverage lookup runs for it. The total is
/// held under a quadratic ceiling: installing borrowed inputs still asks
/// every held view of the block once per view
/// (`ResourceContext::view_occurrences_for_fact`, which must see every
/// candidate to refuse an ambiguous binding), so the total is not yet linear.
/// Its owner check (`ResourceContext::directly_supporting_owned_entry`) asks
/// only the block's owned ranges when no projection support is recorded, so
/// it no longer adds a second `N^2` term.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn contract_entry_with_many_views_beside_an_owner_is_not_cubic() {
    let samples = [4, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = many_viewed_arrays(size, true);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("f.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!("size {size} many-views fixture failed: {}", error.message())
            });
            sample
        })
        .collect::<Vec<_>>();

    let curve = |name: &str| {
        samples
            .iter()
            .map(|sample| ScalingSample {
                size: sample.size,
                work: sample.named_work.get(name).copied().unwrap_or(0),
                named_work: BTreeMap::new(),
            })
            .collect::<Vec<_>>()
    };
    assert_near_linear_scaling(
        "explicit-separation veto beside many views",
        &curve("operation `memory range coverage: explicit separation`"),
    );
    // A quadratic curve quadruples per doubling and a cubic one multiplies
    // by eight; 4.5 separates them with room for fixed-cost noise.
    assert!(
        samples
            .windows(2)
            .skip(1)
            .all(|pair| pair[1].work.saturating_mul(2) <= pair[0].work.saturating_mul(9)),
        "many-views contract entry grows faster than quadratically: {samples:?}; named work: {}",
        named_growth_diagnostic(&samples),
    );
}

/// Unfolding a composite resource whose body holds a constant range exposes
/// its cells as one run, so the proof costs the same whatever the range's
/// length, for scalar elements and for pointer elements (whose cells keep
/// the word their load names). Before, each element was a named cell: at
/// 1000 elements a store after the unfold exhausted the smart budget.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn an_unfolded_constant_composite_range_costs_the_same_whatever_its_length() {
    let c_source = "int32 put(int32 *a) {\n    a[3] = 5;\n    return a[3];\n}\n\nvoid put_pointer(int32 **p, int32 *q) {\n    p[1] = q;\n}\n";
    let click_source = |length: u64, wide: bool| {
        let bounds = if wide {
            format!("0u64..{length}u64")
        } else {
            format!("0..{length}")
        };
        format!(
            "verifying \"put.c\";\n\nresource block(p: int32*) {{ owns p[{bounds}]; }}\nresource pointers(p: int32**) {{ owns p[{bounds}]; }}\n\nint32 put(int32 *a) {{\n    owns block(a);\n    ensures result == 5;\n    ensures a[4] == old(a[4]);\n}} by {{\n    unfold(block(a));\n    step_until(function.exit);\n    fold(block(a));\n    close();\n}}\n\nvoid put_pointer(int32 **p, int32 *q) {{\n    owns pointers(p);\n    ensures p[2] == old(p[2]);\n    ensures p[1] == q;\n}} by {{\n    unfold(pointers(p));\n    step_until(function.exit);\n    fold(pointers(p));\n    close();\n}}\n"
        )
    };
    verify_c_sources(&click_source(8, false), &[("put.c", c_source)]).expect("warm-up verifies");
    // The large pointer arrays need a 64-bit byte span. Compare lengths
    // within each index format so both groups exercise actual stores.
    for (wide, lengths) in [
        (false, [64, 268_435_455]),
        (true, [600_000_000, 1_000_000_000]),
    ] {
        let samples = lengths
            .iter()
            .map(|&length| {
                let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
                    verify_c_sources(&click_source(length, wide), &[("put.c", c_source)])
                });
                verified.unwrap_or_else(|error| {
                    panic!(
                        "a composite range of {length} elements should verify: {}",
                        error.message()
                    )
                });
                (length, work)
            })
            .collect::<Vec<_>>();
        let least = samples
            .iter()
            .map(|(_, work)| *work)
            .min()
            .expect("samples");
        let most = samples
            .iter()
            .map(|(_, work)| *work)
            .max()
            .expect("samples");
        assert!(least > 0, "{samples:?}");
        assert!(
            most - least <= 64,
            "deterministic work depends on the composite range's length: {samples:?}"
        );
    }
}

/// A symbolic read must not make refolding a compact owned range enumerate
/// its slots. Check the current value, the old value at a distinct index,
/// and refusal of the old value when the index may alias the store.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn symbolic_read_refold_and_refusal_do_not_enumerate_range_elements() {
    let c_source = "int32 read_after_store(int32 *a, int32 k) { a[3] = 5; return a[k]; }";
    // Initialize the shared frontend/stdlib caches outside the work samples,
    // as in the constant-index run regression above.
    verify_c_sources(
        "verifying \"read.c\"; int32 read_after_store(int32 *a, int32 k) {
            owns a[0..16]; requires 0 <= k; requires k < 16;
            ensures result == a[k]; }",
        &[("read.c", c_source)],
    )
    .expect("warm-up verifies");
    for (old_value, distinct_index) in [(false, false), (true, true), (true, false)] {
        let samples = [64, 4096, 1_048_576].map(|length| {
            let value = if old_value { "old(a[k])" } else { "a[k]" };
            let distinct = if distinct_index {
                "requires k != 3;"
            } else {
                ""
            };
            let source = format!(
                "verifying \"read.c\";\n\
                 resource block(p: int32*) {{ owns p[0..{length}]; }}\n\
                 int32 read_after_store(int32 *a, int32 k) {{\n\
                   owns block(a); requires 0 <= k; requires k < {length}; {distinct}\n\
                   ensures result == {value};\n\
                 }} by {{ unfold(block(a)); step_until(function.exit); fold(block(a)); close(); }}"
            );
            let (result, sample) = scaling_sample(length, || {
                verify_c_sources(&source, &[("read.c", c_source)])
            });
            if old_value && !distinct_index {
                let error = result.expect_err("the symbolic index may be the changed element");
                assert!(
                    error
                        .message()
                        .contains("the store to `a[3]` may have written"),
                    "{}",
                    error.message()
                );
            } else {
                result.expect("refolding preserves the selected current or unchanged old value");
            }
            let fold_work = sample
                .named_work
                .iter()
                .filter(|(name, _)| name.ends_with("tactic `fold`"))
                .map(|(_, work)| *work)
                .sum::<usize>();
            (length, sample.work, fold_work)
        });
        eprintln!("symbolic refold work old={old_value}, distinct={distinct_index}: {samples:?}");
        let least = samples.iter().map(|(_, work, _)| *work).min().unwrap();
        let most = samples.iter().map(|(_, work, _)| *work).max().unwrap();
        assert!(least > 0);
        assert!(
            most < 30_000,
            "old={old_value}, distinct={distinct_index}: {samples:?}"
        );
        assert!(samples[0].2 > 0, "fold must be measured: {samples:?}");
        for pair in samples.windows(2) {
            assert_eq!(pair[0].2, pair[1].2, "fold enumerated slots: {samples:?}");
            // The failed arithmetic search grows with the bound's bit length
            // (46 units per additional bit), not with the number of elements.
            let bits = (pair[1].0.ilog2() - pair[0].0.ilog2()) as usize;
            assert!(
                pair[1].1 <= pair[0].1 + 64 * bits,
                "old={old_value}: {samples:?}"
            );
        }
    }
}

/// `N` stores `a[ck] = k`, each index bounded by `0 <= ck < n` and none
/// ordered against another, then a claim about the last one.
fn bounded_index_stores(stores: usize) -> (String, String) {
    let indices = (0..stores)
        .map(|index| format!(", int32 c{index}"))
        .collect::<String>();
    let signature = format!("void mark(int32 *a, int32 n{indices})");
    let store_lines = (0..stores)
        .map(|index| format!("    a[c{index}] = {index};\n"))
        .collect::<String>();
    let c_source = format!("{signature} {{\n{store_lines}}}\n");
    let bounds = (0..stores)
        .map(|index| format!("    requires 0 <= c{index};\n    requires c{index} < n;\n"))
        .collect::<String>();
    let last = stores - 1;
    let steps = "    step();\n".repeat(stores);
    let click_source = format!(
        "verifying \"mark.c\";\n\n{signature} {{\n{bounds}    owns a[0..n];\n    \
         ensures a[c{last}] == {last};\n}} by {{\n{steps}    step_until(function.exit);\n    close();\n}}\n"
    );
    (c_source, click_source)
}

/// A straight line of `N` stores to indices that facts bound but do not
/// order. Each store drops the earlier cell it may alias, and deciding that
/// asks whether its index is below or above the cell's; both refusals walk
/// the order facts from the two indices to their shared bound `n`. The walk
/// used to compare every node it reached with every order and condition fact
/// of the context, which holds `2N` bounds, so each store cost the context
/// and the line cost `N^2`: the store rule's work was 2,294, 7,902, 28,334,
/// 106,062 and 408,974 units at 4 to 64 stores, almost all of it offset
/// cancellation. The walk now reads the edges filed under each node
/// (`OrderWalkIndex`), so a store's refusal costs the same beside any number
/// of other indices' bounds: 990, 2,162, 4,506, 9,194 and 18,570 units.
///
/// The difference graph pushes a bound along at most `EDGE_LIMIT` (32)
/// edges. Past that many indices below `n`, `n` is marked truncated and each
/// interval read pulls up to the limit of its neighbours, a fixed extra cost
/// per store: the store rule charges 1,054, 2,230, 4,678 and 9,958 units at
/// 4 to 32 stores, then 30,022, 65,926 and 137,734 at 64 to 256. Each side
/// of the limit is checked for near-linear growth on its own, so the step
/// between them is not read as growth.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 13s"]
fn stores_to_bounded_unordered_indices_are_near_linear() {
    const STORE_WORK: &str = "operation `verification statement: store`";
    // Within the graph's edge limit, then past it.
    const REGIMES: [&[usize]; 2] = [&[4, 8, 16, 32], &[64, 128]];
    let samples = REGIMES
        .concat()
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = bounded_index_stores(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("mark.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "{size} bounded-index stores should verify: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();
    let store_work = samples
        .iter()
        .map(|sample| {
            let work = sample.named_work.get(STORE_WORK).copied().unwrap_or(0);
            assert!(work > 0, "the stores did not run: {sample:?}");
            work
        })
        .collect::<Vec<_>>();
    // A linear curve doubles per doubling; a quadratic one quadruples. The
    // store rule is asked 9/4 at most over the retained doublings, and
    // the whole verification the same, which the old walk exceeded at every
    // size (3.4 to 3.9 per doubling).
    let within = |low: usize, high: usize| high.saturating_mul(4) <= low.saturating_mul(9);
    // The smallest size is setup-dominated, so its doubling is not checked.
    let (below, beyond) = (1..REGIMES[0].len(), REGIMES[0].len()..samples.len());
    for range in [below, beyond] {
        assert!(
            store_work[range.clone()]
                .windows(2)
                .all(|pair| within(pair[0], pair[1])),
            "the store rule's work over bounded unordered indices is not near linear: {store_work:?}; named work: {}",
            named_growth_diagnostic(&samples)
        );
        assert!(
            samples[range]
                .windows(2)
                .all(|pair| within(pair[0].work, pair[1].work)),
            "stores to bounded unordered indices are not near linear: {samples:?}; named work: {}",
            named_growth_diagnostic(&samples)
        );
    }
}

/// [`bounded_index_stores`] with `size_t` indices and length: each index is
/// bounded by `ck < n` alone, and the owned range `a[0..n]` has 64-bit
/// bounds.
fn bounded_size_t_index_stores(stores: usize) -> (String, String) {
    let indices = (0..stores)
        .map(|index| format!(", uint64 c{index}"))
        .collect::<String>();
    let signature = format!("void mark(int32 *a, uint64 n{indices})");
    let store_lines = (0..stores)
        .map(|index| format!("    a[c{index}] = {index};\n"))
        .collect::<String>();
    let c_source = format!("{signature} {{\n{store_lines}}}\n");
    let bounds = (0..stores)
        .map(|index| format!("    requires c{index} < n;\n"))
        .collect::<String>();
    let last = stores - 1;
    let steps = "    step();\n".repeat(stores);
    let click_source = format!(
        "verifying \"mark.c\";\n\n{signature} {{\n{bounds}    owns a[0..n];\n    \
         ensures a[c{last}] == {last};\n}} by {{\n{steps}    step_until(function.exit);\n    close();\n}}\n"
    );
    (c_source, click_source)
}

/// [`stores_to_bounded_unordered_indices_are_near_linear`] over a range with
/// 64-bit bounds. Each store is placed in `a[0..n]` by the wide membership
/// rule, which decides `ck < n` and the range's span limit by keyed
/// lookups, and drops the earlier cells it may alias, none of which is
/// ordered against it. Neither may scan the other indices' bounds.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: wide-index store scaling through 256 indices"]
fn stores_to_bounded_unordered_size_t_indices_are_near_linear() {
    const STORE_WORK: &str = "operation `verification statement: store`";
    // Like the int32 companion, separate the bounded graph's fixed
    // propagation overhead at EDGE_LIMIT from growth within each regime.
    // Include the first index beyond the cap and several larger sizes.
    const REGIMES: [&[usize]; 2] = [&[4, 8, 16, 32], &[33, 64, 128, 256]];
    let samples = REGIMES
        .concat()
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = bounded_size_t_index_stores(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("mark.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "{size} bounded size_t-index stores should verify: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();
    let store_work = samples
        .iter()
        .map(|sample| {
            let work = sample.named_work.get(STORE_WORK).copied().unwrap_or(0);
            assert!(work > 0, "the stores did not run: {sample:?}");
            work
        })
        .collect::<Vec<_>>();
    // A linear curve doubles per doubling; a quadratic one quadruples.
    let within = |low: usize, high: usize| high.saturating_mul(4) <= low.saturating_mul(9);
    for range in [1..REGIMES[0].len(), REGIMES[0].len()..samples.len()] {
        assert!(
            store_work[range.clone()]
                .windows(2)
                .all(|pair| within(pair[0], pair[1])),
            "the store rule's work over bounded unordered size_t indices is not near linear: {store_work:?}; named work: {}",
            named_growth_diagnostic(&samples)
        );
        assert!(
            samples[range]
                .windows(2)
                .all(|pair| within(pair[0].work, pair[1].work)),
            "stores to bounded unordered size_t indices are not near linear: {:?}; named work: {}",
            samples.iter().map(|sample| sample.work).collect::<Vec<_>>(),
            named_growth_diagnostic(&samples)
        );
    }
}

/// `N` calls that each hand the callee the owned window `bytes + index` of
/// an owned `size_t` range: each call splits the caller's range around the
/// window and rejoins it when the window comes back.
fn owned_size_t_window_calls(calls: usize) -> (String, String) {
    let call_lines = "    set_four(bytes + index);\n".repeat(calls);
    let c_source = format!(
        "void set_four(unsigned char *chunk) {{ chunk[0] = 1; }}\n\
         void write(unsigned char *bytes, unsigned long length, unsigned long index) {{\n\
         {call_lines}}}\n"
    );
    let steps = "    step();\n".repeat(calls);
    let click_source = format!(
        "import click::integer;\nverifying \"write.c\";\n\n\
         void set_four(uint8* chunk) {{\n    owns chunk[0..4];\n}}\n\n\
         void write(uint8* bytes, uint64 length, uint64 index) {{\n    \
         requires index <= length;\n    requires 4u64 <= length - index;\n    \
         owns bytes[0..length];\n}} by {{\n{steps}\
             have to_integer(index + 4u64) == to_integer(index) + 4 by {{\n\
                 apply(integer::uint64_add_to_integer(index, 4u64));\n\
                 close();\n\
             }}\n\
             have to_integer(index + 4u64) <= to_integer(length) by close();\n\
             step_until(function.exit);\n\
             close();\n}}\n"
    );
    (c_source, click_source)
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn owned_size_t_window_calls_are_near_linear() {
    let samples = [4, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = owned_size_t_window_calls(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("write.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "{size} owned size_t window calls should verify: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();
    // A linear curve doubles per doubling; a quadratic one quadruples.
    let within = |low: usize, high: usize| high.saturating_mul(4) <= low.saturating_mul(9);
    assert!(
        samples
            .windows(2)
            .skip(1)
            .all(|pair| within(pair[0].work, pair[1].work)),
        "owned size_t window calls are not near linear: {:?}; named work: {}",
        samples.iter().map(|sample| sample.work).collect::<Vec<_>>(),
        named_growth_diagnostic(&samples)
    );
}

/// `N` stores `a[k] = k` to constant indices of one owned array, then a claim
/// about the first, which every later store has to keep.
fn constant_index_stores(stores: usize) -> (String, String) {
    let signature = "void mark(int32 *a)";
    let store_lines = (0..stores)
        .map(|index| format!("    a[{index}] = {index};\n"))
        .collect::<String>();
    let c_source = format!("{signature} {{\n{store_lines}}}\n");
    let steps = "    step();\n".repeat(stores);
    let click_source = format!(
        "verifying \"mark.c\";\n\n{signature} {{\n    owns a[0..{stores}];\n    \
         ensures a[0] == 0;\n}} by {{\n{steps}    step_until(function.exit);\n    close();\n}}\n"
    );
    (c_source, click_source)
}

/// `N` stores `a[ck] = k` to indices one chain of order facts separates,
/// `0 <= c0 < c1 < … < n`, then a claim about the first.
fn chain_ordered_index_stores(stores: usize) -> (String, String) {
    chain_ordered_index_stores_in(stores, false)
}

/// [`chain_ordered_index_stores`] with the stores in the order `a[cN-1]`
/// first, down to `a[c0]` last, which is the index the claim names.
fn chain_ordered_index_stores_descending(stores: usize) -> (String, String) {
    chain_ordered_index_stores_in(stores, true)
}

fn chain_ordered_index_stores_in(stores: usize, descending: bool) -> (String, String) {
    let indices = (0..stores)
        .map(|index| format!(", int32 c{index}"))
        .collect::<String>();
    let signature = format!("void mark(int32 *a, int32 n{indices})");
    let mut order = (0..stores).collect::<Vec<_>>();
    if descending {
        order.reverse();
    }
    let store_lines = order
        .into_iter()
        .map(|index| format!("    a[c{index}] = {index};\n"))
        .collect::<String>();
    let c_source = format!("{signature} {{\n{store_lines}}}\n");
    let mut bounds = "    requires 0 <= c0;\n".to_string();
    for index in 1..stores {
        bounds.push_str(&format!("    requires c{} < c{index};\n", index - 1));
    }
    bounds.push_str(&format!("    requires c{} < n;\n", stores - 1));
    let steps = "    step();\n".repeat(stores);
    let click_source = format!(
        "verifying \"mark.c\";\n\n{signature} {{\n{bounds}    owns a[0..n];\n    \
         ensures a[c0] == 0;\n}} by {{\n{steps}    step_until(function.exit);\n    close();\n}}\n"
    );
    (c_source, click_source)
}

/// Inspect the generated bounds separately from the store framing work.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: cold expansion and replay at multiple store counts"]
fn signed_store_order_expansion_reuses_bounds() {
    for stores in [8, 24, 48] {
        for descending in [false, true] {
            let (c_source, click_source) = chain_ordered_index_stores_in(stores, descending);
            let click_source = click_source.replace("ensures a[c0] == 0;", "ensures 1 == 1;");
            let program = [("mark.c", c_source.as_str())];
            let label = "mark.contract";
            let expanded =
                crate::surface::expand_c_claim_source_by_label(&click_source, &program, label)
                    .unwrap_or_else(|error| panic!("{stores} stores: {}", error.report()));
            let applications = expanded
                .matches("apply(click::integer::int32_less_")
                .count();
            assert!(
                (stores..=5 * stores).contains(&applications),
                "{stores} stores, descending = {descending}, generated {applications} applications:\n{expanded}"
            );
            crate::surface::without_implicit_solve_for_claim(label, || {
                verify_c_sources(&expanded, &program).map_err(|error| error.report())
            })
            .unwrap_or_else(|error| panic!("{error}\n{expanded}"));
        }
    }
}

fn store_line_samples(
    label: &str,
    fixture: impl Fn(usize) -> (String, String),
) -> Vec<ScalingSample> {
    [4, 8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = fixture(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("mark.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!("{size} {label} stores should verify: {}", error.message())
            });
            sample
        })
        .collect()
}

/// The store rule's work in each sample, which has to be nonzero.
fn store_rule_work(samples: &[ScalingSample]) -> Vec<usize> {
    samples
        .iter()
        .map(|sample| {
            let work = sample
                .named_work
                .get("operation `verification statement: store`")
                .copied()
                .unwrap_or(0);
            assert!(work > 0, "the stores did not run: {sample:?}");
            work
        })
        .collect()
}

/// Whether every one of the three largest doublings of `work` grows by at
/// most `numerator / denominator`.
fn doublings_within(work: &[usize], numerator: usize, denominator: usize) -> bool {
    work.windows(2)
        .skip(1)
        .all(|pair| pair[1].saturating_mul(denominator) <= pair[0].saturating_mul(numerator))
}

/// A straight line of `N` stores `a[k] = k` to constant indices. Each store
/// keeps every earlier cell, and it used to ask each one whether it may
/// alias: `N^2/2` questions, 445, 1,225, 3,761, 12,705 and 46,017 units of
/// store work at 4 to 64 stores. A cell whose offset shares the store's
/// anchor and whose constant byte gap clears both accesses is now kept
/// without being asked (`reasoning::store_gap`), so a store visits only the
/// cells within eight bytes of its own: 477, 1,155, 2,587, 5,483 and 11,339
/// units in a debug build, whose check re-asks a few skipped cells per store
/// (467 to 8,959 in release). The claim reads `a[0]`, so every store has to
/// keep it.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn stores_to_constant_indices_are_near_linear() {
    let samples = store_line_samples("constant-index", constant_index_stores);
    let store_work = store_rule_work(&samples);
    // Linear doubles per doubling; the old curve rose 3.1 to 3.6.
    assert!(
        doublings_within(&store_work, 9, 4),
        "the store rule's work over constant indices is not near linear: {store_work:?}; named work: {}",
        named_growth_diagnostic(&samples)
    );
}

/// A straight line of `N` stores `a[ck] = k` whose indices one chain of
/// order facts separates, `0 <= c0 < c1 < … < n`. Each store asks every
/// earlier cell, and each question walks the order chain between its two
/// indices, so the line cost `N^3`: 830, 3,582, 20,494, 139,342 and
/// 1,032,462 units of store work at 4 to 64 stores. The walk now shares what
/// it learns across the questions toward one index (`OrderReachMemo`), so a
/// question costs a constant beyond the first, a store is linear in the
/// cells it keeps, and the line is the `N^2/2` questions themselves: 738,
/// 2,394, 8,506, 31,898 and 123,290 in order, and 900 to 149,372 with the
/// stores in reverse order. A cubic curve multiplies by eight per doubling;
/// the bound admits the quadratic four and rejects that.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5s in the parallel gate"]
fn stores_to_chain_ordered_indices_are_quadratic_not_cubic() {
    for (label, fixture) in [
        (
            "chain-ordered",
            chain_ordered_index_stores as fn(usize) -> (String, String),
        ),
        (
            "reverse chain-ordered",
            chain_ordered_index_stores_descending,
        ),
    ] {
        let samples = store_line_samples(label, fixture);
        let store_work = store_rule_work(&samples);
        assert!(
            doublings_within(&store_work, 17, 4),
            "the store rule's work over {label} indices grows faster than quadratically: {store_work:?}; named work: {}",
            named_growth_diagnostic(&samples)
        );
    }
}

#[test]
fn resource_reference_entry_setup_has_near_linear_work() {
    let samples = [16, 64, 256].map(|count| {
        let mut source = String::from(
            "resource cell() { field revision: int32; }\n\
             resource record(target: cell()) { field revision: int32; }\n\
             void f() { owns target: cell();\n",
        );
        for index in 0..count {
            source.push_str(&format!("owns r{index}: record(target);\n"));
        }
        source.push_str("}\n");
        let file = parser::parse(&source).unwrap();
        let ((context, work), persistent_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                crate::surface::lowering::resource_context_from_requirements(
                    file.function_blocks()[0].requires(),
                    ParameterBinding::default(),
                    &crate::kernel::ExecutionState::new(),
                    &crate::kernel::PureFactContext::new(),
                )
                .unwrap()
            })
        });
        assert_eq!(context.facts().len(), count + 1);
        (count, work, persistent_work)
    });
    assert!(samples[0].1 > 0, "entry setup must be metered: {samples:?}");
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 4, "{samples:?}");
        assert!(
            pair[1].2 <= pair[0].2 * 6,
            "persistent indexes: {samples:?}"
        );
    }
}

/// Each resource clause of a function's entry reads only the parameters it
/// names, so entry setup over one clause per parameter grows with the
/// parameters and not with their square (roadmap/scaling.md, cause 8).
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn entry_resource_clauses_do_not_rebuild_every_parameter() {
    let samples = [16usize, 64, 256].map(|count| {
        let parameters = (0..count)
            .map(|index| format!("int32 x{index}"))
            .collect::<Vec<_>>()
            .join(", ");
        let mut source = format!(
            "resource token(v: int32) {{ field revision: int32; }}\n\
             void f({parameters}) {{\n"
        );
        for index in 0..count {
            source.push_str(&format!("owns t{index}: token(x{index});\n"));
        }
        source.push_str("}\n");
        let file = parser::parse(&source).unwrap();
        let function = &file.function_blocks()[0];
        let program_function =
            syntax::parse_function(&format!("void f({parameters}) {{ }}")).unwrap();
        let arguments = (0..count as u64)
            .map(|index| {
                ProgramExpression::Value(ProgramValue::Int32(OldMachineTerm::Variable(Variable(
                    9_100_000 + index,
                ))))
            })
            .collect::<Vec<_>>();
        let (context, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::surface::lowering::resource_context_from_requirements(
                function.requires(),
                ParameterBinding::new(program_function.parameters(), &arguments),
                &crate::kernel::ExecutionState::new(),
                &crate::kernel::PureFactContext::new(),
            )
            .unwrap()
        });
        assert_eq!(context.facts().len(), count);
        (count, work)
    });
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 6, "{samples:?}");
    }
}

/// `close() using` over a chain of listed order facts adds the premises
/// once each, so its work grows with the chain and not with its square.
/// Both a signed and an unsigned chain are measured at several lengths. The
/// Integer planner its arithmetic tries first searches premise triples only
/// while a chain has at most `MAX_TRIPLE_CLAIMS` premises: a bounded cost
/// both chains pay at short lengths. Past that bound each grows near-linearly.
/// The closers `close() using` tries before arithmetic cost an unsigned chain
/// more than a signed one, so the two chains' peaks are not compared.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: signed and unsigned order-chain scaling across eight complete proofs"]
fn listed_order_chain_arithmetic_is_near_linear_in_the_chain() {
    for (value_type, bound) in [("int32", "4"), ("uint32", "4u32")] {
        let samples = [8usize, 16, 24, 32].map(|edges| {
            let names = (0..edges).map(|index| format!("v{index}")).collect::<Vec<_>>();
            let parameters = names
                .iter()
                .map(|name| format!("{name}: {value_type}"))
                .collect::<Vec<_>>()
                .join(", ");
            let mut facts = names
                .windows(2)
                .map(|pair| format!("{} <= {}", pair[0], pair[1]))
                .collect::<Vec<_>>();
            facts.push(format!("{} < {bound}", names[edges - 1]));
            let requires = facts
                .iter()
                .map(|fact| format!("requires {fact}; "))
                .collect::<String>();
            let listed = facts
                .iter()
                .map(|fact| format!("{fact}; "))
                .collect::<String>();
            let source = format!(
                "theorem chained({parameters}) {{ {requires}ensures v0 < {bound} by {{ close() using {{ {listed}}} }} }}"
            );
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c_sources(&source, &[])
            });
            result.unwrap_or_else(|error| panic!("{edges}-edge chain: {}", error.message()));
            (edges, work)
        });
        eprintln!("{value_type} chain work: {samples:?}");
        for pair in samples[1..].windows(2) {
            assert!(
                pair[1].1 <= pair[0].1.saturating_mul(3),
                "{value_type}: {samples:?}"
            );
        }
    }
}

/// A `step()` written in a loop's `maintain` body is its own simple tactic:
/// it has its own work event and its own simple budget, like a `step()`
/// anywhere else. The preservation driver used to apply it with no tactic
/// open, so every C statement of every path through the body was charged to
/// the enclosing `loop`, whose single budget then capped the whole proof
/// however small each step was. The loop's own work must not grow with what
/// its body steps through.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn preserve_body_steps_are_charged_to_themselves_not_to_the_loop() {
    let sample = |stores: usize| {
        let c_source = format!(
            "void fill(int32 *p, int32 n) {{\n    int32 i = 0;\n    while (i < n) {{\n{}        i = i + 1;\n    }}\n}}\n",
            (0..stores)
                .map(|index| format!("        p[0] = {index};\n"))
                .collect::<String>()
        );
        let click_source = format!(
            "verifying \"fill.c\";

void fill(int32* p, int32 n) {{
    owns p[0..1];
    requires n >= 0;
}} by {{
    step();
    step();
    loop {{
        decreases n - i;
        invariant i >= 0;

        initialize by close();
        maintain by {{
{}        }}
    }}
    step();
    close();
}}
",
            "            step();\n".repeat(stores + 1)
        );
        let (result, events) = crate::instrumentation::collect(|| {
            verify_c_sources(&click_source, &[("fill.c", &c_source)])
        });
        result.unwrap_or_else(|error| {
            panic!("the {stores}-store loop should verify: {}", error.message())
        });
        let finished = |name: &str| {
            events
                .iter()
                .filter_map(|event| match event {
                    crate::instrumentation::VerificationEvent::TacticFinished {
                        tactic,
                        work,
                        ..
                    } if tactic.tactic_name == name => Some(*work),
                    _ => None,
                })
                .collect::<Vec<_>>()
        };
        let loop_work = finished("loop").into_iter().max().unwrap_or(0);
        (stores, finished("step").len(), loop_work)
    };
    let samples = [2, 8, 32, 128].map(sample);
    eprintln!("preserve body work: {samples:?}");
    let (_, base_steps, base_loop_work) = samples[0];
    for &(stores, steps, loop_work) in &samples {
        // The proof is checked the same number of times at every size, so
        // the step events grow by that many per added body statement.
        assert!(
            steps >= base_steps + (stores - 2),
            "every `step()` in the preserve body must report its own work: \
             (stores, step events, loop work) {samples:?}"
        );
        // A few units of frontier bookkeeping per statement, never the
        // statement's own execution.
        assert!(
            loop_work <= base_loop_work + 16 * (stores - 2),
            "the loop must not be charged for the statements its body steps through: \
             (stores, step events, loop work) {samples:?}"
        );
    }
}

/// One loop with `exits` ways out, all holding the same binder: a balanced
/// tree of case splits over `k`, each leaf writing the binder's cell,
/// refolding it, and leaving through a `break`. With `c_branches` the tree is
/// the C's own nested `if`s, so the exits are C paths; without it the C is
/// one store and one `break`, and the exits are the proof's case splits, as
/// in the rbtree insert fixup.
fn loop_with_break_exits(exits: usize, c_branches: bool) -> (String, String) {
    fn c_tree(low: usize, high: usize, indent: usize) -> String {
        let pad = " ".repeat(indent);
        if high - low == 1 {
            return format!("{pad}p->shade = {};\n{pad}break;\n", low % 2);
        }
        let middle = (low + high) / 2;
        format!(
            "{pad}if (k < {middle}) {{\n{}{pad}}} else {{\n{}{pad}}}\n",
            c_tree(low, middle, indent + 4),
            c_tree(middle, high, indent + 4)
        )
    }
    fn proof_tree(low: usize, high: usize, c_branches: bool) -> String {
        if high - low == 1 {
            let color = if !c_branches || low.is_multiple_of(2) {
                "Red"
            } else {
                "Black"
            };
            return format!(
                "step();\nlet c = fold(painted(p), {{ color: Color::{color} }});\nstep();\n"
            );
        }
        let middle = (low + high) / 2;
        let enter = if c_branches { "step();\n" } else { "" };
        format!(
            "if k < {middle} {{\n{enter}{}}} else {{\n{enter}{}}}\n",
            proof_tree(low, middle, c_branches),
            proof_tree(middle, high, c_branches)
        )
    }
    let body = if c_branches {
        c_tree(0, exits, 8)
    } else {
        "        p->shade = 0;\n        break;\n".to_string()
    };
    let c_source = format!(
        "struct node {{ int32 shade; }};\n\nvoid paint(struct node* p, int32 k) {{\n    while (true) {{\n{body}    }}\n}}\n"
    );
    let click_source = format!(
        "verifying \"paint.c\";

spec enum Color {{ Red, Black }}

resource painted(p: struct node*) {{
    field color: Color;
    match color {{
        Color::Red => {{ owns p->shade; fact p->shade == 0; }},
        Color::Black => {{ owns p->shade; fact p->shade == 1; }},
    }}
}}

void paint(struct node* p, int32 k) {{
    owns c: painted(p);
    requires c.color == Color::Black;
}} by {{
    loop {{
        decreases 0;
        owns c: painted(p);
        invariant c.color == Color::Black;

        maintain by {{
            unfold(c);
{}        }}
    }}
    step();
    close();
}}
",
        proof_tree(0, exits, c_branches)
    );
    (c_source, click_source)
}

fn loop_with_break_exits_work(exits: usize, c_branches: bool) -> usize {
    let (c_source, click_source) = loop_with_break_exits(exits, c_branches);
    let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
        verify_c_sources(&click_source, &[("paint.c", &c_source)])
    });
    result.unwrap_or_else(|error| {
        panic!(
            "the loop with {exits} exits should verify: {}",
            error.message()
        )
    });
    work
}

/// Joining a loop's `break` exits costs work proportional to the exits and
/// what each states, not to their pairs. Two steps used to compare every exit
/// with every other and were not charged at all: the exit join's disjunction
/// asked each fact of each exit against every fact of every earlier exit, and
/// the proof layer recorded each exit after comparing it with every exit
/// recorded before it. Each is now a keyed lookup that charges what it reads,
/// so counted work follows the real cost and quadruples, no more, when the
/// exits do.
///
/// Every proof-level case split in the body also read its path's certificate,
/// which walked the proof's whole history back to the root, sibling arms
/// included. Each node now remembers the lineage that ends at it, so a split
/// reads only the nodes added since the last walk that passed, and the walk
/// is charged.
///
/// The bound is on each fourfold step rather than on the whole range, because
/// at these sizes a pairwise term is still a small part of the total: with the
/// exits recorded pairwise again the last step is 4.75 times, and with the
/// history walked in full again it is 9.5 times, against 3.97.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 20s in the parallel gate"]
fn loop_break_exit_join_work_is_near_linear_in_the_exits() {
    let samples =
        [32usize, 128, 512].map(|exits| (exits, loop_with_break_exits_work(exits, false)));
    for pair in samples.windows(2) {
        let ((_, smaller), (_, larger)) = (pair[0], pair[1]);
        assert!(
            larger * 100 <= smaller * 430,
            "loop exit work must be near linear in the exits: (exits, work) {samples:?}"
        );
    }
    // The same exits as paths of the C's own nested branches. Their counted
    // work is the tactics' and is proportional already; what was quadratic
    // there was the uncharged source layout of the branch tree, which this
    // only exercises.
    let branches = [16usize, 64].map(|exits| (exits, loop_with_break_exits_work(exits, true)));
    assert!(
        branches[1].1 * 100 <= branches[0].1 * 430,
        "loop exit work over C branches must be near linear in the exits: {branches:?}"
    );
}

/// A `while (true)` left first by a `break` that never opens the binder and
/// then by `exit_count` `break`s that each write the binder's cell through a
/// helper with a local and fold it back at the same constructor. The join
/// builds its successor from the first exit, which holds its view of the
/// cell once and has called nothing; every writing exit holds that view
/// twice and has ended the helper's local, so each of them reaches the
/// join's normalized resource comparison and its storage-bookkeeping join.
fn loop_with_break_exits_project(exit_count: usize) -> (String, String) {
    let mut c_source = String::from(
        "struct node { int32 shade; };\n\nstatic void repaint(struct node* p) {\n    int32 next = 1;\n    p->shade = next;\n}\n\nvoid paint(struct node* p, int32 flag) {\n    while (true) {\n        if (flag == 0) {\n            break;\n        }\n",
    );
    for exit in 1..exit_count {
        c_source.push_str(&format!(
            "        if (flag == {exit}) {{\n            repaint(p);\n            break;\n        }}\n"
        ));
    }
    c_source.push_str("        repaint(p);\n        break;\n    }\n}\n");

    let mut click_source = String::from(
        "verifying \"exits.c\";\n\nspec enum Color { Red, Black }\n\nresource painted(p: struct node*) {\n    field color: Color;\n    match color {\n        Color::Red => { owns p->shade; fact p->shade == 0; },\n        Color::Black => { owns p->shade; fact p->shade == 1; },\n    }\n}\n\nvoid paint(struct node* p, int32 flag) {\n    owns c: painted(p);\n    requires c.color == Color::Black;\n} by {\n    loop {\n        decreases 0;\n        owns c: painted(p);\n        invariant c.color == Color::Black;\n\n        maintain by {\nif flag == 0 {\nstep();\nstep();\n} else {\n",
    );
    let writing_exit = |click_source: &mut String, skipped: usize| {
        click_source.push_str("unfold(c);\n");
        // Each `if` the path did not take is two steps; the caller adds the
        // taken `if`, when there is one, to `skipped`'s count.
        for _ in 0..skipped {
            click_source.push_str("step();\n");
        }
        click_source
            .push_str("step();\nlet c = fold(painted(p), { color: Color::Black });\nstep();\n");
    };
    for exit in 1..exit_count {
        click_source.push_str(&format!("if flag == {exit} {{\n"));
        writing_exit(&mut click_source, 2 * exit + 1);
        click_source.push_str("} else {\n");
    }
    writing_exit(&mut click_source, 2 * exit_count);
    for _ in 0..exit_count {
        click_source.push_str("}\n");
    }
    click_source.push_str("        }\n    }\n    step();\n    close();\n}\n");
    (c_source, click_source)
}

/// The exit join does one pass over the exits. The body's own steps are
/// charged to themselves and necessarily grow with the square of the exit
/// count here (the `k`th exit is `k` tests deep), so the measure is the
/// `loop` tactic's own work, which is where the join is charged.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4s in the parallel gate"]
fn loop_exit_join_scales_near_linearly_with_the_number_of_exits() {
    // The proof nests one `if` per exit, deeper than a test thread's stack.
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(loop_exit_join_scaling_on_this_thread)
        .expect("the scaling thread starts")
        .join()
        .expect("the scaling thread finishes");
}

fn loop_exit_join_scaling_on_this_thread() {
    let samples = [1, 2, 4, 8]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = loop_with_break_exits_project(size);
            let (verified, mut sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("exits.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!("{size}-exit loop fixture failed: {}", error.message())
            });
            sample.work = sample
                .named_work
                .iter()
                .filter(|(name, _)| name.contains("tactic `loop`"))
                .map(|(_, work)| *work)
                .sum();
            assert!(sample.work > 0, "the loop tactic's work was not measured");
            sample
        })
        .collect::<Vec<_>>();
    assert_near_linear_scaling("loop exits joined", &samples);
    // For B + k*N + a*N^2, 8/3 on increments at 2/4/8
    // rejects a > k/12, just as 3x at 4/8/16 did, while
    // generating fewer of the body's quadratic written steps.
    let earlier = samples[2].work.checked_sub(samples[1].work);
    let later = samples[3].work.checked_sub(samples[2].work);
    assert!(
        matches!((earlier, later), (Some(earlier), Some(later)) if later * 3 <= earlier * 8),
        "loop-exit work increments must remain near linear: {samples:?}"
    );
}

/// Each selected arm follows an earlier checked `have`, rather than a
/// speculative traversal of the complete deferred script before checking it.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.6s in the parallel gate"]
fn post_execution_ifs_with_earlier_haves_have_near_linear_work() {
    let c_source = "int32 pick(int32 a, int32 b) { if (a > b) { return a; } return b; }";
    let mut samples = Vec::new();
    for size in [4, 8, 16, 32] {
        let mut source = String::from(
            "verifying \"pick.c\"; int32 pick(int32 a, int32 b) { requires a > b or a == b; ensures result >= a; } by {",
        );
        // Each C path steps to its exit, then reasons there.
        let reasoning =
            "have old(a) >= old(b); if old(a) >= old(b) { have result >= a; } else {}".repeat(size);
        source.push_str(&format!(
            "if a > b {{ step_until(function.exit); {reasoning} }} else {{ step_until(function.exit); {reasoning} }} }}"
        ));
        let (verified, sample) =
            scaling_sample(size, || verify_c_sources(&source, &[("pick.c", c_source)]));
        verified.unwrap_or_else(|error| panic!("{size} post-execution ifs: {}", error.message()));
        samples.push(sample);
    }
    assert_near_linear_scaling("post-execution ifs after checked haves", &samples);
}

/// A function proof with `count` proof-level `if`s in a row between two C
/// statements. Each `if` only reasons: both arms prove the same fact.
fn sequential_reasoning_ifs_project(count: usize) -> (String, String) {
    let c_source =
        "int32 bump(int32 x) {\n    int32 a;\n    a = 0;\n    a = a + 1;\n    return a;\n}\n"
            .to_string();
    let mut click_source = String::from(
        "verifying \"ifs.c\";\n\nint32 bump(int32 x) {\n    ensures result == 1;\n} by {\n    step();\n    step();\n",
    );
    for index in 0..count {
        click_source.push_str(&format!(
            "    if x <= {index} {{\n        have x <= {index} or x > {index} by {{ close(); }}\n    }} else {{\n        have x <= {index} or x > {index} by {{ close(); }}\n    }}\n"
        ));
    }
    click_source.push_str("    step();\n    step();\n    close();\n}\n");
    (c_source, click_source)
}

/// A proof-level `if` whose arms only reason rejoins, so what follows it is
/// checked once. Before the join each case ran the rest of the proof itself,
/// and `n` such `if`s in a row cost `2^n` runs of the tail; twenty of them
/// would not finish.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn sequential_proof_ifs_rejoin_instead_of_doubling_the_rest_of_the_proof() {
    let samples = [5, 10, 20, 40]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = sequential_reasoning_ifs_project(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("ifs.c", c_source.as_str())])
            });
            verified
                .unwrap_or_else(|error| panic!("{size}-`if` fixture failed: {}", error.message()));
            sample
        })
        .collect::<Vec<_>>();
    assert_near_linear_scaling("sequential proof-level ifs", &samples);
}

/// A function of `count` assignments, proved with one proof-level `if`
/// around each: both arms step the assignment and prove the same fact.
fn sequential_stepping_ifs_project(count: usize) -> (String, String) {
    let mut c_source = String::from("int32 bump(int32 x) {\n    int32 a;\n");
    let mut click_source = String::from(
        "verifying \"ifs.c\";\n\nint32 bump(int32 x) {\n    ensures result == 0;\n} by {\n    step();\n",
    );
    for index in 0..count {
        c_source.push_str("    a = 0;\n");
        click_source.push_str(&format!(
            "    if x <= {index} {{\n        step();\n        have x <= {index} or x > {index} by {{ close(); }}\n    }} else {{\n        step();\n        have x <= {index} or x > {index} by {{ close(); }}\n    }}\n"
        ));
    }
    c_source.push_str("    return a;\n}\n");
    click_source.push_str("    step();\n    close();\n}\n");
    (c_source, click_source)
}

/// Arms that run the same C statement end at one program point in one
/// state, so they rejoin as arms that only reason do.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn sequential_proof_ifs_that_step_c_rejoin_instead_of_doubling() {
    let samples = [5, 10, 20, 40]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = sequential_stepping_ifs_project(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("ifs.c", c_source.as_str())])
            });
            verified
                .unwrap_or_else(|error| panic!("{size}-`if` fixture failed: {}", error.message()));
            sample
        })
        .collect::<Vec<_>>();
    assert_near_linear_scaling("sequential proof-level ifs that step C", &samples);
}

/// A function of `count` stores through `p`, proved with one proof-level
/// `if ... ensuring` around each. Both arms open the slot, step the store,
/// and fold the slot again under differently spelled models, so every `if`
/// rejoins through its interface.
fn sequential_interface_joins_project(count: usize) -> (String, String) {
    let mut c_source =
        String::from("struct cell { int32 value; };\n\nint32 bump(struct cell *p, int32 x) {\n");
    let mut click_source = String::from(
        "verifying \"joins.c\";\n\nresource slot(p: struct cell*) {\n    field model: int32;\n    owns p->value;\n    fact p->value == model;\n}\n\nint32 bump(struct cell* p, int32 x) {\n    requires p != 0;\n    owns c: slot(p);\n    ensures result == 0;\n} by {\n",
    );
    for index in 0..count {
        c_source.push_str(&format!("    p->value = {index};\n"));
        click_source.push_str(&format!(
            "    if x <= {index} ensuring {{\n        owns c: slot(p);\n    }} then {{\n        unfold(c);\n        step();\n        let c = fold(slot(p), {{ model: {index} }});\n    }} else {{\n        unfold(c);\n        step();\n        let c = fold(slot(p), {{ model: p->value }});\n    }}\n"
        ));
    }
    c_source.push_str("    return 0;\n}\n");
    click_source.push_str("    step();\n    close();\n}\n");
    (c_source, click_source)
}

/// A run of interface joins costs in proportion to its length: each join
/// checks its own arms and does not pay again for the joins before it.
///
/// This fixture's arms cache one read each, under the spelling the store
/// uses, so it holds the line on the ordinary case. It did not reproduce the
/// cost the `__rb_insert` port met, where an arm's statements reach cells
/// through pointers loaded from memory; `examples/rbtree/rbtree-insert` is the
/// evidence for that one.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4s in the parallel gate"]
fn sequential_interface_joins_scale_with_their_number() {
    let samples = [5, 10, 20, 40]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = sequential_interface_joins_project(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("joins.c", c_source.as_str())])
            });
            verified
                .unwrap_or_else(|error| panic!("{size}-join fixture failed: {}", error.message()));
            sample
        })
        .collect::<Vec<_>>();
    assert_near_linear_scaling("sequential interface joins", &samples);
}

/// A function that stores to each of `count` fields of one struct.
fn field_stores_project(count: usize) -> (String, String) {
    let fields = (0..count)
        .map(|index| format!("    int32 f{index};\n"))
        .collect::<String>();
    let mut c_source = format!("struct big {{\n{fields}}};\n\nint32 run(struct big *q) {{\n");
    let mut click_source = String::from(
        "verifying \"stores.c\";\n\nint32 run(struct big* q) {\n    requires q != 0;\n",
    );
    for index in 0..count {
        click_source.push_str(&format!("    owns q->f{index};\n"));
    }
    click_source.push_str("    ensures result == 0;\n} by {\n");
    for index in 0..count {
        c_source.push_str(&format!("    q->f{index} = {index};\n"));
        click_source.push_str("    step();\n");
    }
    c_source.push_str("    return 0;\n}\n");
    click_source.push_str("    step();\n    close();\n}\n");
    (c_source, click_source)
}

/// Recording how a stepped store reads in source terms must not rewrite the
/// memory state the store's fact carries. It used to restore every load
/// the fact mentioned, the cached values of that state included, one name
/// at a time and copying the state each time: the square of the known
/// cells for every `step()`. The restored form is only read for a comparison
/// that names a qualified object, and these name none.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2s in the parallel gate"]
fn stepping_a_store_does_not_rewrite_the_memory_its_fact_carries() {
    for size in [16, 64] {
        let (c_source, click_source) = field_stores_project(size);
        let (verified, sample) = scaling_sample(size, || {
            verify_c_sources(&click_source, &[("stores.c", c_source.as_str())])
        });
        verified.unwrap_or_else(|error| panic!("{size}-store fixture failed: {}", error.message()));
        let rewrites = sample
            .named_work
            .get("operation `substitution: state rewrite`")
            .copied()
            .unwrap_or(0);
        assert_eq!(
            rewrites, 0,
            "{size} field stores spent {rewrites} work units rewriting memory states"
        );
    }
}

/// A counting loop whose `maintain` proof makes `count` proof-level case
/// splits in a row before closing the invariants. Both arms of each only
/// reason.
fn loop_body_reasoning_ifs_project(count: usize) -> (String, String) {
    let c_source = String::from(
        "int32 spin(int32 n, int32 x) {\n    int32 i;\n    i = 0;\n    while (i < n) {\n        i = i + 1;\n    }\n    return 0;\n}\n",
    );
    let mut click_source = String::from(
        "verifying \"ifs.c\";\n\nint32 spin(int32 n, int32 x) {\n    requires n >= 0;\n    ensures result == 0;\n} by {\n    step();\n    step();\n    loop {\n        decreases n - i;\n        invariant 0 <= i and i <= n;\n\n        initialize by close();\n        maintain by {\n            step();\n",
    );
    for index in 0..count {
        click_source.push_str(&format!(
            "            if x <= {index} {{\n                have x <= {index} or x > {index} by {{ close(); }}\n            }} else {{\n                have x <= {index} or x > {index} by {{ close(); }}\n            }}\n"
        ));
    }
    click_source.push_str("        }\n    }\n    step();\n    close();\n}\n");
    (c_source, click_source)
}

/// Proof-level splits in a loop body rejoin as they do in a function body,
/// so the rest of the iteration is checked once. Each case used to run the
/// rest of the body itself, to the back edge, and `n` splits in a row cost
/// `2^n` runs of it; twenty would not finish.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn sequential_proof_ifs_in_a_loop_body_rejoin_instead_of_doubling() {
    let samples = [5, 20, 40]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = loop_body_reasoning_ifs_project(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("ifs.c", c_source.as_str())])
            });
            verified
                .unwrap_or_else(|error| panic!("{size}-`if` fixture failed: {}", error.message()));
            sample
        })
        .collect::<Vec<_>>();
    assert_near_linear_scaling_at_sampled_sizes(
        "sequential proof-level ifs in a loop body",
        &samples,
    );
}

/// A scanning loop whose body is `count` C `if`s in a row, each storing to
/// a local when its guard holds, with no written `maintain` proof.
fn loop_body_c_ifs_project(count: usize) -> (String, String) {
    let ifs = (0..count)
        .map(|index| {
            format!(
                "        if (a[{index}] == 7) {{\n            found = {};\n        }}\n",
                index + 1
            )
        })
        .collect::<String>();
    let c_source = format!(
        "int32 scan(int32* a, int32 n) {{\n    int32 i;\n    int32 found;\n    i = 0;\n    found = 0;\n    while (i < n) {{\n{ifs}        i = i + 1;\n    }}\n    return 0;\n}}\n"
    );
    let click_source = format!(
        "verifying \"scan.c\";\n\nint32 scan(int32* a, int32 n) {{\n    views a[0..{count}];\n    requires 0 <= n;\n    requires n <= {count};\n    ensures result == 0;\n}} by {{\n    step();\n    step();\n    step();\n    step();\n    loop {{\n        decreases n - i;\n        invariant 0 <= i and i <= n;\n    }}\n    step();\n    close();\n}}\n"
    );
    (c_source, click_source)
}

/// The automatic loop closer joins the arms of a C `if` that both fall
/// through, so the rest of the body is walked once. It used to walk the
/// rest once per arm: `n` such `if`s in a row cost `2^n` paths, and their
/// expansion wrote all of them out.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn the_automatic_loop_closer_joins_c_branches_instead_of_walking_every_path() {
    let samples = [4, 16, 32]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = loop_body_c_ifs_project(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("scan.c", c_source.as_str())])
            });
            verified
                .unwrap_or_else(|error| panic!("{size}-`if` fixture failed: {}", error.message()));
            sample
        })
        .collect::<Vec<_>>();
    assert_near_linear_scaling_at_sampled_sizes(
        "C ifs in an automatically closed loop body",
        &samples,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn atomic_memory_evidence_cites_only_connected_conditions() {
    use crate::kernel::{
        Address, AddressOffset, OldConditionTerm, OldMachineTerm, Proposition, PureFactContext,
        SymbolicMemory, Variable,
    };

    let memory = SymbolicMemory::new();
    // The address of element `variable` of the goal's array.
    let at = |variable: u64| {
        Address::new(
            "goal".into(),
            AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(variable)), 4),
        )
    };
    let loadable = |base: Address, bytes: u32| Proposition::MemoryLoadable {
        point: Default::default(),
        memory: memory.clone(),
        base,
        bytes: (OldMachineTerm::constant(bytes)).into(),
        wide: false,
    };
    let equal = |left: u64, right: u64| {
        Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(OldMachineTerm::Variable(Variable(left))),
                right: Box::new(OldMachineTerm::Variable(Variable(right))),
            },
            true,
        )
    };
    // (sources, goal, premises the certificate cites; none when unproved)
    let cases = [
        (
            "a covering range",
            vec![loadable(at(470_000), 16)],
            loadable(at(470_000).offset_by_bytes(4), 4),
            Some(1),
        ),
        (
            "a non-null source without other non-null objects",
            vec![
                loadable(Address::symbolic(Variable(470_002)), 16),
                Proposition::condition_is(
                    OldConditionTerm::address_equal(
                        Address::symbolic(Variable(470_002)),
                        Address::null(),
                    ),
                    false,
                ),
            ],
            loadable(Address::symbolic(Variable(470_002)).offset_by_bytes(4), 4),
            Some(1),
        ),
        (
            "a range at an equal index",
            vec![loadable(at(470_001), 16), equal(470_000, 470_001)],
            loadable(at(470_000), 16),
            Some(2),
        ),
        (
            "a range at an index not known equal",
            vec![loadable(at(470_001), 16)],
            loadable(at(470_000), 16),
            None,
        ),
    ];
    for (name, sources, goal, cited) in cases {
        let samples = [16usize, 32, 64, 128]
            .into_iter()
            .map(|unrelated| {
                let mut context = PureFactContext::new();
                for index in 0..unrelated as u64 {
                    context = context
                        .assume_proposition(equal(471_000 + 2 * index, 471_001 + 2 * index))
                        .assume_proposition(Proposition::condition_is(
                            OldConditionTerm::address_equal(
                                Address::symbolic(Variable(475_000 + index)),
                                Address::null(),
                            ),
                            false,
                        ))
                        .assume_proposition(Proposition::MemoryLoadable {
                            point: Default::default(),
                            memory: memory.clone(),
                            base: Address::new(
                                format!("other{index}").as_str().into(),
                                AddressOffset::constant(0),
                            ),
                            bytes: (OldMachineTerm::constant(16)).into(),
                            wide: false,
                        });
                }
                for source in &sources {
                    context = context.assume_proposition(source.clone());
                }
                let (derivation, work) = crate::instrumentation::measure_deterministic_work(|| {
                    crate::kernel::search::ProofSearch::derive_atomic_proposition(&(context), &goal)
                });
                let mut check_work = 0;
                let mut certificate_bytes = 0;
                let premises = match (cited, derivation) {
                    (Some(cited), Some(derivation)) => {
                        let premises = derivation.context_premises();
                        assert_eq!(premises.len(), cited, "{name}: {premises:?}");
                        assert!(premises.iter().all(|premise| sources.contains(premise)));
                        certificate_bytes = format!("{premises:?}").len();
                        let (valid, work) =
                            crate::instrumentation::measure_deterministic_work(|| {
                                derivation.check(&context)
                            });
                        assert!(valid, "{name}: kernel rejected retained leaf");
                        check_work = work;
                        for omitted in &premises {
                            let without = sources
                                .iter()
                                .filter(|source| *source != omitted)
                                .cloned()
                                .fold(PureFactContext::new(), PureFactContext::assume_proposition);
                            assert!(
                                !derivation.check(&without),
                                "{name}: omitted required premise accepted"
                            );
                        }
                        premises.len()
                    }
                    (None, None) => 0,
                    (cited, derivation) => panic!(
                        "{name}: expected {cited:?} cited premises, derived {}",
                        derivation.is_some()
                    ),
                };
                (unrelated, premises, work, check_work, certificate_bytes)
            })
            .collect::<Vec<_>>();
        eprintln!("{name}: unrelated/premises/planning/check/bytes {samples:?}");
        for sample in &samples {
            assert_eq!(
                sample.4, samples[0].4,
                "certificate bytes grew: {samples:?}"
            );
            assert!(
                sample.3 <= samples[0].3 + 8,
                "checker work grew: {samples:?}"
            );
            assert!(
                sample.2 <= samples[0].2 + 8,
                "planner work grew: {samples:?}"
            );
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].2 <= pair[0].2.saturating_mul(3),
                "{name}: derivation work is superlinear: {samples:?}"
            );
        }
    }
}

#[test]
fn atomic_load_dependencies_ignore_other_state_cells() {
    use crate::kernel::{
        Address, AddressOffset, OldConditionTerm, OldMachineTerm, ProgramValue, Proposition,
        PureFactContext, SymbolicMemory, Variable,
    };

    let index_cell = Address::new("selected-index".into(), AddressOffset::constant(0));
    let index = OldMachineTerm::Variable(Variable(490_000));
    let equality = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(index.clone()),
            right: Box::new(OldMachineTerm::constant(2)),
        },
        true,
    );
    let mut samples = Vec::new();
    for size in [8usize, 16, 32, 64] {
        let mut memory =
            SymbolicMemory::new().store(index_cell.clone(), ProgramValue::Int32(index.clone()));
        let mut context = PureFactContext::new();
        for i in 0..size {
            let value = OldMachineTerm::Variable(Variable(491_000 + i as u64));
            memory = memory.store(
                Address::new(
                    format!("other-cell-{i}").as_str().into(),
                    AddressOffset::constant(0),
                ),
                ProgramValue::Int32(value.clone()),
            );
            context = context.assume_proposition(Proposition::condition_is(
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(value),
                    right: Box::new(OldMachineTerm::constant(7)),
                },
                true,
            ));
        }
        let at = |value| {
            Address::new(
                "selected-array".into(),
                AddressOffset::scaled_int32_node(value, 4),
            )
        };
        let source = Proposition::MemoryLoadable {
            point: Default::default(),
            memory: memory.clone(),
            base: at(OldMachineTerm::constant(2)),
            bytes: (OldMachineTerm::constant(4)).into(),
            wide: false,
        };
        let goal = Proposition::MemoryLoadable {
            point: Default::default(),
            memory: memory.clone(),
            base: at(OldMachineTerm::read_named(
                crate::kernel::ProgramPoint::of_memory(&memory),
                Box::new(index_cell.clone()),
                crate::kernel::LoadKind::Int32,
            )),
            bytes: (OldMachineTerm::constant(4)).into(),
            wide: false,
        };
        context = context
            .assume_proposition(source.clone())
            .assume_proposition(equality.clone());
        let (proof, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::search::ProofSearch::derive_atomic_proposition(&(context), &goal)
        });
        let proof = proof.expect("the addressed index's equality should suffice");
        assert_eq!(proof.context_premises().len(), 2);
        assert!(
            proof
                .context_premises()
                .iter()
                .all(|p| p == &source || p == &equality)
        );
        assert!(proof.check(&context));
        for single in [&source, &equality] {
            assert!(!proof.check(&PureFactContext::new().assume_proposition(single.clone())));
        }
        samples.push((size, work));
    }
    // Cold state canonicalization may read the supplied state. Its
    // size is explicit input; the retained ambient conditions stay bounded.
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 2, "{samples:?}");
    }
}

/// A goal no single source decides is proved from the facts connected to it
/// and cites only those: here a quantified fact and the bound its
/// instantiation needs, beside unrelated conditions and memory facts. This
/// goal used to be proved from, and cite, the whole context.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn atomic_evidence_without_one_source_cites_connected_facts() {
    use crate::kernel::{
        Address, AddressOffset, OldConditionTerm, OldMachineTerm, Proposition, PureFactContext,
        Sort, SymbolicMemory, Variable,
    };

    let memory = SymbolicMemory::new();
    let load = |offset: AddressOffset| {
        OldMachineTerm::read_named(
            crate::kernel::ProgramPoint::at(&(crate::kernel::intern_memory_ref(&memory))),
            Box::new(Address::new("data".into(), offset)),
            crate::kernel::LoadKind::Int32,
        )
    };
    let equal = |left: OldMachineTerm, right: OldMachineTerm| {
        Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(left),
                right: Box::new(right),
            },
            true,
        )
    };
    let less = |left: OldMachineTerm, right: OldMachineTerm, holds: bool| {
        Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(left),
                right: Box::new(right),
            },
            holds,
        )
    };
    let variable = |id: u64| OldMachineTerm::Variable(Variable(id));
    let index = Variable(480_000);
    // forall index. index < exit ==> data[index] == index
    let quantified = crate::kernel::quantifiers::test_forall(
        Default::default(),
        index,
        Sort::ProgramInt32,
        Proposition::Implies(
            Box::new(less(variable(480_000), variable(480_001), true)),
            Box::new(equal(
                load(AddressOffset::scaled_int32_node(variable(480_000), 4)),
                variable(480_000),
            )),
        ),
    );
    // not (exit < 3), so index 2 is below exit.
    let bound = less(variable(480_001), OldMachineTerm::constant(3), false);
    let goal = equal(
        load(AddressOffset::constant(8)),
        OldMachineTerm::constant(2),
    );
    let context = |unrelated: u64, with_bound: bool| {
        let mut context = PureFactContext::new();
        for index in 0..unrelated {
            context = context
                .assume_proposition(less(
                    variable(481_000 + 2 * index),
                    variable(481_001 + 2 * index),
                    true,
                ))
                .assume_proposition(Proposition::MemoryLoadable {
                    point: Default::default(),
                    memory: memory.clone(),
                    base: Address::new(
                        format!("other{index}").as_str().into(),
                        AddressOffset::scaled_int32_node(variable(482_000 + index), 4),
                    ),
                    bytes: (OldMachineTerm::constant(16)).into(),
                    wide: false,
                });
        }
        context = context.assume_proposition(quantified.clone());
        if with_bound {
            context = context.assume_proposition(bound.clone());
        }
        context
    };
    let samples = [16u64, 32, 64, 128]
        .into_iter()
        .map(|unrelated| {
            let available = context(unrelated, true);
            let (derivation, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::search::ProofSearch::derive_atomic_proposition(&(available), &goal)
            });
            let derivation = derivation.expect("the instantiated fact derives the goal");
            let premises = derivation.context_premises();
            assert_eq!(premises.len(), 2, "{premises:?}");
            assert!(premises.contains(&quantified) && premises.contains(&bound));
            let certificate_bytes = format!("{premises:?}").len();
            let (valid, check_work) =
                crate::instrumentation::measure_deterministic_work(|| derivation.check(&available));
            assert!(valid);
            assert!(!derivation.check(&context(unrelated, false)));
            assert!(!derivation.check(&PureFactContext::new().assume_proposition(bound.clone())));
            // Without the bound the instantiation's guard is not known.
            assert!(
                crate::kernel::search::ProofSearch::derive_atomic_proposition(
                    &(context(unrelated, false)),
                    &goal
                )
                .is_none()
            );
            (unrelated, work, check_work, certificate_bytes)
        })
        .collect::<Vec<_>>();
    eprintln!("fallback: unrelated/planning/check/bytes {samples:?}");
    for sample in &samples {
        assert_eq!(
            sample.3, samples[0].3,
            "certificate bytes grew: {samples:?}"
        );
        assert!(
            sample.2 <= samples[0].2 + 8,
            "checker work grew: {samples:?}"
        );
        assert!(
            sample.1 <= samples[0].1 + 8,
            "planner work grew: {samples:?}"
        );
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "derivation work is superlinear: {samples:?}"
        );
    }
    // Extend one context before each fallback query. A cache of whole-context
    // collections would still do quadratic work across this sequence.
    let extensions = [8usize, 16, 32, 64].map(|steps| {
        let mut available = context(0, true);
        crate::kernel::search::proposition_search::reset_condition_selection_visits();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for step in 0..steps {
                available = available
                    .clone()
                    .assume_proposition(less(
                        variable(483_000 + 2 * step as u64),
                        variable(483_001 + 2 * step as u64),
                        true,
                    ))
                    .assume_proposition(Proposition::MemoryLoadable {
                        point: Default::default(),
                        memory: memory.clone(),
                        base: Address::new(
                            format!("extension{step}").as_str().into(),
                            AddressOffset::constant(0),
                        ),
                        bytes: (OldMachineTerm::constant(16)).into(),
                        wide: false,
                    });
                let proof = crate::kernel::search::ProofSearch::derive_atomic_proposition(
                    &(available),
                    &goal,
                )
                .expect("connected fallback");
                assert_eq!(proof.context_premises().len(), 2);
                assert!(proof.check(&available));
            }
        });
        let visits = crate::kernel::search::proposition_search::condition_selection_visits();
        assert!(
            visits <= steps * 4,
            "unrelated conditions visited: {steps}, {visits}"
        );
        (steps, work)
    });
    eprintln!("incremental fallback: extensions/work {extensions:?}");
    for pair in extensions.windows(2) {
        assert!(pair[1].1 <= pair[0].1.saturating_mul(3), "{extensions:?}");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn atomic_retained_evidence_expands_without_unrelated_conditions() {
    let cases = [
        (
            "covering",
            "requires viewable(p[0..4]);",
            "viewable(p[1..2])",
            "requires viewable(p[0..4]);",
        ),
        (
            "adjacent",
            "requires viewable(p[0..2]); requires viewable(p[2..4]);",
            "viewable(p[0..4])",
            "requires viewable(p[2..4]);",
        ),
        (
            "alias",
            "requires p == q; requires viewable(p[0..4]);",
            "viewable(q[1..2])",
            "requires p == q;",
        ),
        (
            "resource",
            "requires separate(memory(p[0..4]), memory(q[0..4]));",
            "separate(memory(p[0..4]), memory(q[0..4]))",
            "requires separate(memory(p[0..4]), memory(q[0..4]));",
        ),
        (
            "quantified fallback",
            "requires forall (k: int32) { k < exit implies p[k] == k }; requires not (exit < 3);",
            "p[2] == 2",
            "requires not (exit < 3);",
        ),
    ];
    for (name, sources, goal, required) in cases {
        let mut verification = Vec::new();
        let mut expansions = Vec::new();
        let mut rechecks = Vec::new();
        let mut body_sizes = Vec::new();
        for size in [4, 8, 16, 32] {
            let parameters = std::iter::once("p: int32[], q: int32[], exit: int32".to_string())
                .chain((0..size).map(|index| format!("u{index}: int32[], x{index}: int32")))
                .collect::<Vec<_>>()
                .join(", ");
            let requirements = (0..size)
                .map(|index| {
                    format!("requires viewable(u{index}[0..4]); requires x{index} < 1000;")
                })
                .collect::<Vec<_>>()
                .join("\n");
            let source = format!(
                "theorem leaf({parameters}) {{ {requirements} {sources} ensures {goal} by {{ close(); }} }}"
            );
            let (result, sample) = scaling_sample(size, || verify_click_theorems(&source));
            result.unwrap_or_else(|error| panic!("{name}/{size}: {}", error.message()));
            verification.push(sample);
            let position = expansion::position_at_offset(&source, source.find("close();").unwrap());
            let (expanded, sample) = scaling_sample(size, || {
                expand_c_tactic_source_at(&source, &[], position.line, position.column)
            });
            let expanded = expanded
                .unwrap_or_else(|error| panic!("{name}/{size} expansion: {}", error.message()));
            let body = &expanded[expanded.find("by {").unwrap()..];
            assert!(!body.contains("solve();"), "{body}");
            for index in 0..size {
                assert!(
                    !body.contains(&format!("u{index}")) && !body.contains(&format!("x{index}")),
                    "{name}: unrelated premise retained: {body}"
                );
            }
            body_sizes.push(body.len());
            expansions.push(sample);
            let (result, sample) = scaling_sample(size, || verify_click_theorems(&expanded));
            result.unwrap_or_else(|error| panic!("{name}/{size} recheck: {}", error.message()));
            rechecks.push(sample);
            assert!(
                verify_click_theorems(&expanded.replace(required, "")).is_err(),
                "{name}: omitted required premise accepted"
            );
        }
        assert!(
            body_sizes.iter().all(|size| *size == body_sizes[0]),
            "{name}: expanded certificate grew: {body_sizes:?}"
        );
        assert_near_linear_scaling(name, &verification);
        assert_near_linear_scaling(name, &expansions);
        assert_near_linear_scaling(name, &rechecks);
    }
}

/// A failing `solve` over a chain `x0 <= x1 <= ... <= xN` does about the same
/// work however long the chain is. Its bound selection visits a fixed
/// number of variables and plans the certificate before spelling a premise,
/// and its upper-bound split nests a fixed number of times, reads its
/// candidates from the goal variables' bound buckets, and looks for
/// spellings at a fixed number of program points.
///
/// The split used to recurse along the whole chain, each arm running the
/// whole closure again: 44, 76, 140, and 268 runs of the closure's last
/// route at 4, 8, 16, and 32, and 127565, 300253, 579237, and 1180213 units
/// on 2026-10-05. Bounded, the same sizes take 53224, 67088, 68480, and
/// 71264 units (2026-10-06).
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn failing_solve_work_is_flat_along_a_variable_chain() {
    let solve_work = |sample: &ScalingSample| {
        sample
            .named_work
            .iter()
            .filter(|(name, _)| name.ends_with("tactic `solve`"))
            .map(|(_, work)| *work)
            .sum::<usize>()
    };
    let sources = |size: usize| {
        let c_parameters = (0..=size)
            .map(|index| format!("int x{index}"))
            .collect::<Vec<_>>()
            .join(", ");
        let parameters = (0..=size)
            .map(|index| format!("int32 x{index}"))
            .collect::<Vec<_>>()
            .join(", ");
        let requires = (0..size)
            .map(|index| format!("    requires x{index} <= x{};\n", index + 1))
            .collect::<String>();
        (
            format!("int chain({c_parameters}) {{\n    return 0;\n}}\n"),
            format!(
                "verifying \"chain.c\";\n\nint32 chain({parameters}) {{\n    requires 0 <= x0;\n{requires}    requires x{size} <= 100;\n    ensures x0 + 1 <= 50;\n}}\n"
            ),
        )
    };
    let mut work = Vec::new();
    // Keep the short initialization/control case and the original 8/32 guard.
    for size in [4, 8, 32] {
        let (c_source, click_source) = sources(size);
        let (verified, sample) = scaling_sample(size, || {
            verify_c_sources(&click_source, &[("chain.c", c_source.as_str())])
        });
        assert!(
            verified.is_err(),
            "`x0 + 1 <= 50` does not follow at size {size}"
        );
        work.push(solve_work(&sample));
    }
    assert!(work[0] > 0, "{work:?}");
    assert!(
        *work.last().unwrap() <= work[1].saturating_add(work[1] / 4),
        "a failing solve's work grew with the chain past the bounded sizes: {work:?}"
    );
}

/// The `step_until(function.exit); close();` proof of [`early_return_fan_out`] written with
/// simple tactics only, as `click expand` writes it: the steps and C
/// branches the execution takes, then one closer per path under the same nested conditions. A returned constant
/// closes by `known`; the two `-1` returns transport the postcondition
/// from `function.exit`, since `result` cannot be named in an earlier
/// state.
fn early_return_fan_out_explicit_proof(returns: usize) -> String {
    fn indent(depth: usize) -> String {
        "    ".repeat(depth + 1)
    }
    let condition = |index: usize| {
        let statement = 7 + 3 * index;
        format!("at(region({statement}).entry, a) == at(region({statement}).entry, {index})")
    };
    let transported = "have result == a or result == -1 by { close(); }\n{i}close();\n";
    let mut proof = String::from(
        "verifying \"fan_out.c\";\n\nint g(int a) {\n    ensures result == a or result == -1;\n} by {\n    step();\n    step();\n    if at(region(2).entry, p) == at(region(2).entry, 0) {\n        step();\n        step();\n    } else {\n        step();\n        step();\n        step();\n        step();\n",
    );
    for index in 0..returns {
        let i = indent(index + 1);
        proof.push_str(&format!(
            "{i}if {} {{\n{i}    step();\n{i}    step();\n{i}}} else {{\n{i}    step();\n{i}    step();\n",
            condition(index)
        ));
    }
    proof.push_str(&format!("{}step();\n", indent(returns + 1)));
    for index in (0..returns).rev() {
        proof.push_str(&format!("{}}}\n", indent(index + 1)));
    }
    proof.push_str("    }\n    if at(region(2).entry, p) == at(region(2).entry, 0) {\n");
    proof.push_str(&format!(
        "        {}",
        transported.replace("{i}", "        ")
    ));
    proof.push_str("    } else {\n");
    for index in 0..returns {
        let i = indent(index + 1);
        proof.push_str(&format!(
            "{i}if {} {{\n{i}    have result == a or result == -1 by {{\n{i}        close();\n{i}    }}\n{i}    close();\n{i}}} else {{\n",
            condition(index)
        ));
    }
    let i = indent(returns + 1);
    proof.push_str(&format!("{i}{}", transported.replace("{i}", &i)));
    for index in (0..returns).rev() {
        proof.push_str(&format!("{}}}\n", indent(index + 1)));
    }
    proof.push_str("    }\n}\n");
    proof
}

/// Return preparation and contract preparation share checked contexts in both
/// proof forms. Bound whole-transaction construction, not just one tactic.
/// Both forms must also keep whole-verification work and retained fact storage
/// near linear, at candidate publication and at checked completion.
fn check_completed_early_return_context_reuse(explicit: bool) {
    let mut samples = Vec::new();
    let mut transport = Vec::new();
    let mut execute = Vec::new();
    let mut finalization = Vec::new();
    let mut spelling = Vec::new();
    let mut selection = Vec::new();
    let mut outcome_reads = Vec::new();
    let mut terminal_reads = Vec::new();
    let mut statement_entries = Vec::new();
    let mut stored = Vec::new();
    let mut entries = Vec::new();
    let mut contract_entries = Vec::new();
    let mut allocation_resolution = Vec::new();
    let mut return_context = Vec::new();
    for returns in [4, 8, 16, 32, 64] {
        let c = early_return_fan_out(returns);
        let click = if explicit {
            early_return_fan_out_explicit_proof(returns)
        } else {
            concat!(
                "verifying \"fan_out.c\";\n",
                "int g(int a) { ensures result == a or result == -1; } ",
                "by { step_until(function.exit); close(); }",
            )
            .to_string()
        };
        let before = crate::kernel::reasoning::path_facts::context_rebuild_entries();
        let contract_before = crate::kernel::reasoning::path_facts::contract_path_context_entries();
        crate::surface::proof::take_outcome_fact_reads();
        crate::surface::proof::take_terminal_publication_visits();
        crate::kernel::proof::take_statement_priority_entries();
        let ((verified, sample), storage) =
            crate::kernel::ExecutionFacts::measure_published_storage(|| {
                scaling_sample(returns, || {
                    verify_c_sources(&click, &[("fan_out.c", c.as_str())])
                })
            });
        for sample in &storage {
            assert!(
                sample.paths >= returns,
                "missing completed storage measurement: {storage:?}"
            );
            assert!(
                sample.fact_values <= 4 * returns + 16,
                "shared path facts, explicit={explicit}: {storage:?}"
            );
        }
        stored.push(storage);
        verified.unwrap_or_else(|error| {
            panic!(
                "{returns} returns, explicit={explicit}: {}",
                error.message()
            )
        });
        entries.push(crate::kernel::reasoning::path_facts::context_rebuild_entries() - before);
        contract_entries.push(
            crate::kernel::reasoning::path_facts::contract_path_context_entries() - contract_before,
        );
        allocation_resolution.push(
            sample
                .named_work
                .get("operation `branch allocation resolution`")
                .copied()
                .unwrap_or(0),
        );
        return_context.push(
            sample
                .named_work
                .get("operation `statement return context`")
                .copied()
                .unwrap_or(0),
        );
        outcome_reads.push(crate::surface::proof::take_outcome_fact_reads());
        terminal_reads.push(crate::surface::proof::take_terminal_publication_visits());
        statement_entries.push(crate::kernel::proof::take_statement_priority_entries());
        if !explicit {
            if returns <= 32 {
                finalization.push(ScalingSample {
                    size: returns,
                    work: *sample
                        .named_work
                        .get("operation `implicit empty effect check`")
                        .unwrap_or_else(|| {
                            panic!(
                                "fan-out did not reach the implicit empty-effect check: {sample:?}"
                            )
                        }),
                    named_work: BTreeMap::new(),
                });
            }
            execute.push(ScalingSample {
                size: returns,
                work: *sample
                    .named_work
                    .get("smart tactic `execute`")
                    .unwrap_or_else(|| panic!("the fan-out was not run by `execute`: {sample:?}")),
                named_work: BTreeMap::new(),
            });
            transport.push(ScalingSample {
                size: returns,
                work: *sample
                    .named_work
                    .get("operation `solve closure: state transport`")
                    .unwrap_or_else(|| panic!("solve did not try a state transport: {sample:?}")),
                named_work: BTreeMap::new(),
            });
            spelling.push(ScalingSample {
                size: returns,
                work: *sample
                    .named_work
                    .get("operation `solve closure: premise raising`")
                    .unwrap_or(&0),
                named_work: BTreeMap::new(),
            });
            selection.push(
                *sample
                    .named_work
                    .get("operation `atomic dependency selection`")
                    .unwrap_or(&0),
            );
        }
        samples.push(sample);
    }
    eprintln!("stored execution facts, explicit={explicit}: {stored:?}");
    for pair in stored.windows(2).skip(2) {
        for (before, after) in pair[0].iter().zip(&pair[1]) {
            assert!(
                after.fact_values * 100 <= before.fact_values * 240,
                "stored fact objects must scale near linearly: {stored:?}"
            );
            assert!(
                after.vector_chunks * 100 <= before.vector_chunks * 260,
                "stored vector chunks must scale near linearly: {stored:?}"
            );
            assert!(
                after.logical_facts > after.fact_values,
                "the fixture must share prefixes between paths: {stored:?}"
            );
        }
    }
    eprintln!(
        "context reuse explicit={explicit}: {samples:?}; entries: {entries:?}; contract entries: {contract_entries:?}"
    );
    assert!(
        contract_entries
            .windows(2)
            .all(|pair| pair[1] <= pair[0] * 2 + 8),
        "contract preparation must reuse contexts: explicit={explicit}, {contract_entries:?}"
    );
    // Small explicit proofs may complete without the branch-step driver.
    // Require the largest case to exercise it, so absent instrumentation
    // cannot turn every measured cost into zero.
    if explicit {
        assert!(
            samples
                .last()
                .unwrap()
                .named_work
                .contains_key("operation `branch allocation resolution`")
        );
    }
    // Once malloc is resolved, later branches must not rebuild their growing
    // local fact lists merely to ask allocation resolution to do nothing.
    // Compare the largest sizes, after the explicit driver starts running;
    // resolving the initial malloc has a fixed setup cost.
    eprintln!("branch allocation resolution explicit={explicit}: {allocation_resolution:?}");
    assert!(
        allocation_resolution
            .windows(2)
            .skip(2)
            .all(|pair| pair[1] <= pair[0] + 8),
        "settled allocations must not rebuild branch contexts: {allocation_resolution:?}"
    );
    if explicit {
        assert!(
            samples
                .last()
                .unwrap()
                .named_work
                .contains_key("operation `statement return context`")
        );
        assert!(
            return_context
                .windows(2)
                .all(|pair| pair[1] <= pair[0] * 2 + 8),
            "returns must reuse their checked local prefix: {return_context:?}"
        );
    }
    assert!(
        entries.windows(2).all(|pair| pair[1] <= pair[0] * 2 + 32),
        "return and completion contexts must share their prefix: explicit={explicit}, {entries:?}"
    );
    assert!(
        samples
            .windows(2)
            .skip(2)
            .all(|pair| pair[1].work * 100 <= pair[0].work * 225),
        "whole verification must retain shared history and context savings: explicit={explicit}, {samples:?}; {}",
        named_growth_diagnostic(&samples)
    );
    eprintln!(
        "outcome fact reads explicit={explicit}: {outcome_reads:?}; terminal visits: {terminal_reads:?}"
    );
    for ((returns, (reused, imported)), (shared, visited)) in [4, 8, 16, 32, 64]
        .into_iter()
        .zip(&outcome_reads)
        .zip(&terminal_reads)
    {
        assert_eq!(
            *reused,
            returns + 2,
            "every checked leaf retains its context, explicit={explicit}"
        );
        assert!(
            *imported <= 4 * returns + 8,
            "outcome imports must read only local effects, explicit={explicit}: {outcome_reads:?}"
        );
        assert!(
            *shared >= returns && *visited <= 4 * returns + 16,
            "terminal publication must retain subtrees, explicit={explicit}: {terminal_reads:?}"
        );
    }
    for pair in outcome_reads.windows(2) {
        assert!(
            pair[1].1 * 100 <= pair[0].1 * 225,
            "logical imports grew quadratically, explicit={explicit}: {outcome_reads:?}"
        );
    }
    eprintln!("stored statement priority entries, explicit={explicit}: {statement_entries:?}");
    // A statement may select a subset of its checked cases, so its ordered
    // batch cannot always borrow the entire prefix. Bound total storage and
    // the number of materialized multi-fact batches, so an input-sized list
    // may occur at a fixed number of transitions, never once per return.
    for (returns, (entries, largest, nonlocal)) in
        [4, 8, 16, 32, 64].into_iter().zip(statement_entries)
    {
        assert!(
            largest <= returns + 8 && nonlocal <= 16,
            "statement batches must not multiply guard chains: explicit={explicit}, returns={returns}, largest={largest}, nonlocal={nonlocal}"
        );
        assert!(
            entries <= 16 * returns + 32,
            "checked leaf contexts must share case prefixes: explicit={explicit}, returns={returns}, entries={entries}"
        );
    }
    if explicit {
        // Keep every original 8/16/32/64 proof and its whole-work guard.
        assert_near_linear_scaling("an explicit early-return proof", &samples[1..]);
    } else {
        // Retain the original grouped-finalization 4/8/16/32 regression.
        // Its pre-fix per-theorem rescans cost 30/90/306/1122 units;
        // visiting each path once cost 6/10/18/34 instead.
        eprintln!("implicit empty-effect check work: {finalization:?}");
        assert_near_linear_scaling("implicit empty-effect check over paths", &finalization);
        eprintln!("fan-out execute work: {execute:?}");
        assert_near_linear_scaling("executing a fan-out's paths", &execute);
        eprintln!("fan-out state transport work: {transport:?}");
        assert_near_linear_scaling("solve's state transport search", &transport);
        eprintln!("fan-out premise raising work: {spelling:?}");
        assert_near_linear_scaling("solve's premise raising", &spelling);
        eprintln!("indexed fan-out: {samples:?}; selection: {selection:?}");
        assert!(
            selection.windows(2).all(|pair| pair[1] <= pair[0] * 2 + 8),
            "indexed constant selection must stay linear: {selection:?}"
        );
        assert!(
            samples
                .windows(2)
                .skip(2)
                .all(|pair| pair[1].work * 100 <= pair[0].work * 215),
            "whole verification must retain the selection saving: {samples:?}; {}",
            named_growth_diagnostic(&samples)
        );
        let c = early_return_fan_out(64);
        let false_click =
            "verifying \"fan_out.c\";\nint g(int a) { ensures result == a or result == -2; }";
        let error = verify_c_sources(false_click, &[("fan_out.c", c.as_str())])
            .expect_err("indexed premises cannot prove an incorrect postcondition");
        assert!(!error.message().contains("budget"), "{}", error.message());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: shared full-size early-return regression matrix"]
fn completed_early_return_contexts_are_reused_for_certification() {
    std::thread::Builder::new()
        .name("fan-out-context-reuse".into())
        .stack_size(64 << 20)
        .spawn(|| {
            let _ = roundtrip_sample(1, 0);
            for explicit in [false, true] {
                check_completed_early_return_context_reuse(explicit);
            }
        })
        .expect("spawn the context-reuse thread")
        .join()
        .expect("context-reuse thread");
}

fn check_early_return_execution_expansion(returns: usize) {
    std::thread::Builder::new()
        .name("fan-out-expansion".into())
        // Match the existing fan-out tests and unoptimized fixture workers.
        .stack_size(64 << 20)
        .spawn(move || {
            let click = "verifying \"fan_out.c\";\n\nint g(int a) {\n    ensures result == a or result == -1;\n}\n";
            let c = early_return_fan_out(returns);
            let sources = [("fan_out.c", c.as_str())];
            // This fixture has an implicit proof: select the function's claim,
            // not the former execute() location beyond the end of its source.
            let expanded = expand_function_proof_source(click, &sources, "g")
                .unwrap_or_else(|error| panic!("{returns} returns expand: {}", error.message()));
            assert_ne!(expanded, click, "the implicit proof must become explicit");
            assert!(!expanded.contains("execute()"));
            verify_c_sources(&expanded, &sources)
                .unwrap_or_else(|error| panic!("{returns} returns reverify: {}", error.message()));
            let false_c = c.replace("    return -1;\n}", "    return -2;\n}");
            assert_ne!(false_c, c);
            let false_sources = [("fan_out.c", false_c.as_str())];
            verify_c_sources(&expanded, &false_sources)
                .expect_err("the last path still owes its postcondition");
            verify_c_sources(&early_return_fan_out_explicit_proof(returns), &false_sources)
                .expect_err("an explicit proof cannot accept a false final path");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn early_return_execution_expansion_reverifies_16_returns() {
    check_early_return_execution_expansion(16);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn early_return_execution_expansion_reverifies_32_returns() {
    check_early_return_execution_expansion(32);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 12.2s for 64-return expansion and false-final-path checks"]
fn early_return_execution_expansion_reverifies_64_returns() {
    check_early_return_execution_expansion(64);
}

#[test]
fn long_proof_else_spines_parse_on_a_small_stack_and_restore_block_bindings() {
    std::thread::Builder::new()
        .name("proof-else-parser".into())
        .stack_size(2 << 20)
        .spawn(|| {
            let mut body = "close();".to_string();
            for index in 0..64 {
                body = format!("if 0 == 0 {{ close(); }} else {{ let v{index} = obtain(exists (k: Integer) {{ k == k }}); {body} }} let v{index} = obtain(exists (k: int32) {{ k == k }});");
            }
            parser::parse_file_items(&format!("theorem spine() {{ ensures 0 == 0 by {{ {body} }} }}"))
                .expect("else scopes restore their existential bindings before later tactics");
            let mut body = "close();".to_string();
            for _ in 0..=parser::STRUCTURAL_NESTING_LIMIT {
                body = format!("if 0 == 0 {{ {body} }} else {{ close(); }}");
            }
            let error = parser::parse_file_items(&format!("theorem deep() {{ ensures 0 == 0 by {{ {body} }} }}"))
                .expect_err("recursive then arms remain bounded");
            assert!(error.message().contains("proof nesting exceeds Click's supported depth"));
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A linear goal that one stated fact decides is proved by arithmetic from
/// selected premises before `solve` searches chains of rewrites through the
/// equalities connected to the goal's atoms, so each such equality costs a
/// constant. Measured 2026-11-11: about 3,300 units an equality (27,041 at
/// 4, 66,431 at 16). With the chain search first the same goals cost 54,008
/// at 4 and 364,310 at 16, and six equalities beside a loop's invariants
/// exhausted the two-million budget.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn a_linear_goal_costs_a_constant_per_equality_connected_to_its_atoms() {
    for size in [4usize, 16, 32] {
        let parameters = (0..size)
            .map(|i| format!(", k{i}: uint64"))
            .collect::<String>();
        let equalities = (0..size)
            .map(|i| format!("    requires k{i} == q - r;\n"))
            .collect::<String>();
        let source = format!(
            "theorem bounded(q: uint64, r: uint64{parameters}) {{\n    \
             requires q <= 4611686018427387903u64;\n    requires r <= q;\n{equalities}    \
             ensures q - r <= 4611686018427387903u64 by {{ close(); }}\n}}\n"
        );
        let limits = crate::instrumentation::TacticWorkLimits {
            smart: 30_000 + 5_000 * size,
            ..crate::instrumentation::TacticWorkLimits::default()
        };
        crate::instrumentation::with_tactic_work_limits(limits, || verify_click_theorems(&source))
            .unwrap_or_else(|error| panic!("{size} equalities: {}", error.message()));
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn recorded_value_names_index_only_the_locals_each_point_changes() {
    use crate::kernel::{OldMachineTerm, Variable};
    let point = |index| ProgramPointRef {
        region: CodeRegionRef::Region(index),
        kind: ProgramPointKind::Exit,
    };
    let value = |index: usize| OldMachineTerm::Variable(Variable(700_000 + index as u64));
    let schema = crate::kernel::ResourceFieldSchema::new(vec![(
        "size".into(),
        crate::kernel::ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap();
    let block_pointer = |index: usize| {
        Address::new(
            crate::kernel::AddressBase::Symbolic(Variable(800_000 + index as u64)),
            AddressOffset::constant(0),
        )
    };
    for size in [16usize, 64, 256, 1024] {
        let mut retained_states = RecordedStates::new();
        let mut state = ExecutionState::new()
            .with_memory(crate::kernel::SymbolicMemory::new().with_block("cells", 4 * size as u32));
        let mut insert_work = Vec::new();
        for index in 0..size {
            // Each point binds one new local, and from the second on also
            // gives local `x0` a new value: with `p` below, three changed
            // locals, one new instance and one stored cell per point.
            state = state.with_local(
                format!("x{}", index + 1),
                ProgramValue::Int32(value(2 * index)),
            );
            if index > 0 {
                state = state.with_local("x0", ProgramValue::Int32(value(2 * index + 1)));
            }
            // And local `p` a pointer into a block of its own, and a new
            // resource instance with one field.
            state = state.with_local(
                "p",
                ProgramValue::typed_pointer(block_pointer(index), ProgramType::Int32Pointer),
            );
            let resources =
                state
                    .resources()
                    .clone()
                    .unchecked_with_fact(crate::kernel::ResourceFact::own(
                        crate::kernel::Resource::Instance(
                            crate::kernel::ResourceInstance::new(
                                InstanceId::from_variable(Variable(900_000 + index as u64)),
                                "object".into(),
                                vec![].into(),
                                schema.clone(),
                                vec![crate::kernel::AlgebraicValue::Program(ProgramValue::Int32(
                                    value(4 * size + index),
                                ))]
                                .into(),
                            )
                            .unwrap(),
                        ),
                    ));
            state = state.with_resource_context(resources);
            // And one memory cell a new value.
            let memory = state.memory().clone().store(
                Address::new(
                    crate::kernel::AddressBase::Concrete("cells".into()),
                    AddressOffset::constant(4 * index as i64),
                ),
                ProgramValue::Int32(value(6 * size + index)),
            );
            state = state.with_memory(memory);
            let (((), work), persistent) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    retained_states.insert(point(index), state.clone());
                })
            });
            insert_work.push(work + persistent);
        }
        let height = (usize::BITS - size.leading_zeros()) as usize;
        let last = *insert_work.last().unwrap();
        assert!(
            last <= 24 * height + 64,
            "size {size}: the last insert changed three locals, one instance and one cell and did {last} work"
        );
        // The first value `x0` held is named at the point that recorded it,
        // though `x0` holds a newer value now; the newest one at its point.
        for (term, expected) in [(value(3), point(1)), (value(2 * size - 1), point(size - 1))] {
            let (named, work) = crate::instrumentation::measure_deterministic_work(|| {
                retained_states
                    .point_naming_integer(&term)
                    .map(|(selector, name, _)| (selector.clone(), name.to_string()))
            });
            assert_eq!(
                named,
                Some((ProgramPointSelector::from(expected), "x0".to_string()))
            );
            assert!(work <= 4, "size {size}: naming one value did {work} work");
        }
        // A value no recorded local held has no name.
        assert!(
            retained_states
                .point_naming_integer(&value(10 * size))
                .is_none()
        );
        // The first pointer `p` held is found by its block at its point.
        let first = block_pointer(0);
        let (points, work) = crate::instrumentation::measure_deterministic_work(|| {
            retained_states
                .points_holding_address_base(&first.base)
                .map(|(selector, _)| selector.clone())
                .collect::<Vec<_>>()
        });
        assert_eq!(points, vec![ProgramPointSelector::from(point(0))]);
        assert!(work <= 4, "size {size}: naming one pointer did {work} work");
        // The value the first point stored is found by its fingerprint.
        let (cells, work) = crate::instrumentation::measure_deterministic_work(|| {
            retained_states
                .points_holding_cell_integer(&value(6 * size))
                .map(|(selector, _)| selector.clone())
                .collect::<Vec<_>>()
        });
        assert_eq!(cells, vec![ProgramPointSelector::from(point(0))]);
        assert!(
            work <= 4,
            "size {size}: naming one cell value did {work} work"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 10.1s in the parallel gate"]
fn callback_parsing_and_explicit_steps_scale_with_written_calls() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/rb_augment_callbacks_helper_owns.md");
    let fixture = crate::cli::read_mdtest(&path).unwrap();
    let click = fixture.click_source.unwrap();
    let baseline_sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c_sources(&click, &baseline_sources).unwrap();
    let samples = [1, 2, 4, 8].map(|count| {
        let statements = "    augment->propagate(parent, 0);\n".repeat(count);
        let sources = fixture
            .c_sources
            .iter()
            .map(|(name, source)| {
                (
                    name.clone(),
                    source.replace("    augment->propagate(parent, 0);\n", &statements),
                )
            })
            .collect::<Vec<_>>();
        let sources = sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let source = click.replace(
            "step_until(function.exit);",
            &"step(); ".repeat(3 * (count + 2) + 1),
        );
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            verify_c_sources(&source, &sources)
        });
        result.unwrap_or_else(|error| panic!("{count} callback statements: {}", error.message()));
        work
    });
    assert!(samples[0] > 0);
    // For B + k*N + a*N^2, 20/9 on increments at 2/4/8
    // rejects a > k/48, as did 12/5 at 4/8/16. Fixed
    // setup cannot mask the same quadratic callback work.
    let earlier = samples[2].checked_sub(samples[1]);
    let later = samples[3].checked_sub(samples[2]);
    assert!(
        matches!((earlier, later), (Some(earlier), Some(later)) if later * 9 <= earlier * 20),
        "callback work increments must remain near linear: {samples:?}"
    );
    for pair in samples.windows(2) {
        assert!(
            pair[1] * 2 <= pair[0] * 5,
            "callback source steps must scale with their written calls: {samples:?}"
        );
    }
}

fn byte_view_narrowing_sources() -> (&'static str, &'static str) {
    let c_source = r#"void narrow(const unsigned char *bytes, int index) {
    int unrelated;
    unrelated = index;
    return;
}
"#;
    let contract = r#"verifying "range-narrowing.c";
void narrow(const uint8* bytes, int32 index) {
 requires 0 <= index;
 requires index <= 22204;
 views bytes[0..22208];
 ensures 0 == 0;
} by {
 step_until(assignment(unrelated, 0).entry); step();
 have 0 <= index by { close(); }
 have to_integer(index + 4) <= 22208 by { close() using { 0 <= index; index <= 22204; } }
 have to_integer(index) <= to_integer(index + 4) by { close() using { 0 <= index; index <= 22204; to_integer(index + 4) <= 22208; } }
 have viewable(bytes[0..22208]) by { close(); }
 have contains(memory(bytes[0..22208]), memory(bytes[index..index + 4])) by {
  apply(click::separation::contains_subrange(bytes, 0, 22208, index, index + 4));
 }
 have viewable(bytes[index..index + 4]) by {
  apply(click::separation::viewable_restrict(memory(bytes[0..22208]), memory(bytes[index..index + 4])));
 }
 step_until(function.exit); close();
}
"#;
    (c_source, contract)
}

// A store must not expand an unrelated shared byte view to narrow four bytes.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4.1s in the parallel gate"]
fn explicit_byte_view_narrowing_keeps_large_seeded_ranges_compact() {
    let (c_source, contract) = byte_view_narrowing_sources();
    let samples = [16u32, 64, 4096, 22208, 1048576].map(|size| {
        let source = contract
            .replace("22208", &size.to_string())
            .replace("22204", &(size - 4).to_string());
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            verify_c_sources(&source, &[("range-narrowing.c", c_source)])
        });
        result.unwrap_or_else(|error| panic!("size {size}: {}", error.message()));
        (size, work)
    });
    assert!(
        samples.iter().all(|(size, work)| {
            // The containment and restriction applications recheck the
            // encoded bounds. Permit logarithmic work in the range length.
            *work <= samples[0].1 + 1280 * (size.ilog2() - samples[0].0.ilog2()) as usize
        }),
        "range length must not materialize cells: {samples:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: byte-view authority sidecar mutations"]
fn explicit_byte_view_narrowing_rejects_missing_authority_and_bounds() {
    let (c_source, contract) = byte_view_narrowing_sources();
    for (before, after) in [
        ("views bytes[0..22208];", ""),
        ("requires index <= 22204;", ""),
        (
            "viewable(bytes[index..index + 4])",
            "viewable(bytes[index..index + 5])",
        ),
    ] {
        let invalid = contract.replace(before, after);
        assert_ne!(invalid, contract);
        let error = verify_c_sources(&invalid, &[("range-narrowing.c", c_source)])
            .expect_err("invalid range authority was accepted");
        assert!(
            !error.message().contains("budget exhausted"),
            "{}",
            error.message()
        );
    }
}

/// Explicit framing must refuse locally even as unrelated scalar premises grow.
/// The mdtest pins one refusal. Check that looking up the selected separation
/// stays bounded as the proof accumulates premises.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 6s for four explicit frame refusals"]
fn explicit_frame_refusal_scales_with_unrelated_facts() {
    let mdtest = crate::cli::parse_mdtest(
        std::path::Path::new("explicit_preserve_failure_is_prompt.md"),
        include_str!("../../../../mdtests/explicit_preserve_failure_is_prompt.md"),
    )
    .unwrap();
    let mut samples = Vec::new();
    for size in [8, 16, 32, 64] {
        let parameters = (0..size)
            .map(|index| format!(", int32 extra{index}"))
            .collect::<String>();
        let premises = (0..size)
            .map(|index| format!("    requires extra{index} == 0;\n"))
            .collect::<String>();
        let signature = "struct region* region, int32 value, int32 k";
        let extended = format!("{signature}{parameters}");
        let source = mdtest
            .click_source
            .as_deref()
            .unwrap()
            .replace(signature, &extended)
            .replace(
                "    requires r.end <= st.capacity;",
                &format!("{premises}    requires r.end <= st.capacity;"),
            );
        let c_sources = mdtest
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.replace(signature, &extended)))
            .collect::<Vec<_>>();
        let c_refs = c_sources
            .iter()
            .map(|(name, source)| (*name, source.as_str()))
            .collect::<Vec<_>>();
        let (result, sample) = scaling_sample(size, || {
            crate::instrumentation::with_tactic_work_limits(
                crate::instrumentation::TacticWorkLimits {
                    simple: 250_000,
                    control: 250_000,
                    ..crate::instrumentation::TacticWorkLimits::default()
                },
                || verify_c_sources(&source, &c_refs),
            )
        });
        let error = result.expect_err("a missing frame is still refused");
        assert!(
            error
                .message()
                .contains("preserve separation is not exactly available"),
            "{size}: {error:?}"
        );
        samples.push(sample);
    }
    assert_near_linear_scaling_with_increment_bound(
        "explicit frame refusal with unrelated facts",
        &samples,
    );
    // The selected preservation check pays only a fixed amount per added premise.
    // Whole-run totals also include shared frontend initialization.
    for pair in samples.windows(2) {
        let before = pair[0].named_work["simple tactic `have`"];
        let after = pair[1].named_work["simple tactic `have`"];
        assert!(
            after <= before + 6 * (pair[1].size - pair[0].size),
            "{samples:?}"
        );
    }
}

/// Expanding a closer into one `known` per returned field used to retry
/// an unchanged failed whole-contract transition for every field. Count that
/// operation across increasing output frontiers, independently of its cost.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 9s across four complete named-resource callers"]
fn consecutive_resource_closers_attempt_one_transition() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/call_frames_pointer_after_named_unfolds.md");
    let fixture = crate::cli::read_mdtest(&path).unwrap();
    let original = fixture.click_source.unwrap();
    let (c_name, original_c) = &fixture.c_sources[0];
    let mut previous = None;
    for size in [1, 4, 8] {
        let c_source = original_c.replace(
            "struct node *left;",
            &format!("struct node *left; int32 extra[{size}];"),
        );
        let mut source = original.replace(
            "    fact p->left == 0;",
            &format!("    owns p->extra[0..{size}];\n    fact p->left == 0;"),
        );
        let outputs = (0..size)
            .map(|index| format!("    produces p->extra[{index}]; produces q->extra[{index}];\n"))
            .collect::<String>();
        source = source.replace(
            "    produces *anchor;",
            &(outputs + "    produces *anchor;"),
        );
        let tail = source
            .rfind("    unfold(c);\n}")
            .expect("caller ends by unfolding its returned cursor")
            + "    unfold(c);".len();
        source.insert_str(
            tail,
            &format!("\n    step(); {}", "close(); ".repeat(8 + 2 * size)),
        );
        let (verified, events) = crate::instrumentation::collect(|| {
            verify_c_sources(&source, &[(c_name.as_str(), c_source.as_str())])
        });
        verified.unwrap_or_else(|error| panic!("size={size}: {}", error.message()));
        let checks = events
            .iter()
            .filter(|event| {
                matches!(event,
                    crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                        if name == "return resources: definitional check"
                )
            })
            .count();
        assert!(checks > 0);
        if let Some(previous) = previous {
            assert_eq!(
                checks, previous,
                "size={size}: retries grew with resource closers"
            );
        }
        previous = Some(checks);
    }
}

/// The shared-heap probe's reference resources and retain helper, verbatim.
fn shared_parent_retain_declarations() -> (&'static str, &'static str) {
    let source = include_str!("../../../../design/shared-heap-probes/shared_parent.click");
    let declarations = &source
        [source.find("authorized resource child_ref").unwrap()..source.find("verifying").unwrap()];
    let retain = &source
        [source.find("void child_retain").unwrap()..source.find("void child_release").unwrap()];
    (declarations, retain)
}

/// One child retained `count` times by explicit call steps: each step adds
/// one reference to the same population.
fn repeated_retain_project(count: usize) -> (String, String) {
    let (declarations, retain) = shared_parent_retain_declarations();
    let c_source = format!(
        "struct child {{\n    int32 refs;\n    int32 payload;\n}};\n\nvoid child_retain(struct child* obj) {{\n    obj->refs = obj->refs + 1;\n}}\n\nvoid retain_many(struct child* obj) {{\n{}}}\n",
        "    child_retain(obj);\n".repeat(count)
    );
    let click_source = format!(
        "{declarations}verifying \"retain.c\";\n\n{retain}void retain_many(struct child* obj) {{\n    requires count(child_ref(obj)) < {};\n    owns child_control(obj);\n    owns child_ref(obj);\n{}}} by {{\n{}    step();\n    close();\n}}\n",
        2147483647 - count,
        "    produces child_ref(obj);\n".repeat(count),
        "    step(child_retain);\n".repeat(count),
    );
    (c_source, click_source)
}

/// Explicit retains of one shared child cost in proportion to their number:
/// a step does not pay again for the references the earlier ones produced.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: shared-child retain scaling"]
fn repeated_retains_of_one_child_scale_with_their_number() {
    let samples = [1, 2, 4, 8]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = repeated_retain_project(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("retain.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!("{size}-retain fixture failed: {}", error.message())
            });
            sample
        })
        .collect::<Vec<_>>();
    assert_near_linear_scaling("repeated retains of one child", &samples);
    // Remove the fixed helper/entry cost before checking the larger
    // increments. For B + k*N + a*N^2, 28/11 at 2/4/8 rejects
    // a > k/16, as did 20/7 at 4/8/16 before reducing the sizes.
    let earlier = samples[2].work.checked_sub(samples[1].work);
    let later = samples[3].work.checked_sub(samples[2].work);
    assert!(
        matches!((earlier, later), (Some(earlier), Some(later)) if later * 11 <= earlier * 28),
        "repeated-retain work increments must remain near linear: {samples:?}"
    );
}

/// One retain of a child while `count` other children, each with its own
/// reference population and control, stay live and untouched.
fn retain_amid_unrelated_children_project(count: usize) -> (String, String) {
    let (declarations, retain) = shared_parent_retain_declarations();
    let parameters = (0..count)
        .map(|index| format!(", struct child* other{index}"))
        .collect::<String>();
    let c_source = format!(
        "struct child {{\n    int32 refs;\n    int32 payload;\n}};\n\nvoid child_retain(struct child* obj) {{\n    obj->refs = obj->refs + 1;\n}}\n\nvoid retain_one(struct child* obj{parameters}) {{\n    child_retain(obj);\n}}\n"
    );
    let unrelated = (0..count)
        .map(|index| {
            format!("    owns child_control(other{index});\n    owns child_ref(other{index});\n")
        })
        .collect::<String>();
    let click_source = format!(
        "{declarations}verifying \"retain.c\";\n\n{retain}void retain_one(struct child* obj{parameters}) {{\n    requires count(child_ref(obj)) < 2147483647;\n    owns child_control(obj);\n    owns child_ref(obj);\n    produces child_ref(obj);\n{unrelated}}} by {{\n    step(child_retain, {{}});\n    step();\n    close();\n}}\n"
    );
    (c_source, click_source)
}

/// A retain does not pay for the unrelated shared children that are live:
/// every pointer parameter shares one memory block, so a lookup that walks
/// that block instead of the queried object's own facts grows with them.
fn assert_retain_ignores_unrelated_live_children(sizes: [usize; 5]) -> Vec<ScalingSample> {
    const CALLER: &str = "retain_one";
    const HELPER: &str = "child_retain";
    let (base_c, base_click) = retain_amid_unrelated_children_project(sizes[0]);
    assert_eq!(base_c.matches(CALLER).count(), 1);
    assert_eq!(base_click.matches(CALLER).count(), 1);
    let c_helper = &base_c[..base_c.find(CALLER).unwrap()];
    let click_helper = &base_click[..base_click.find(CALLER).unwrap()];
    {
        let checked = crate::surface::verify_c_sources_functions(
            &base_click,
            &[("retain.c", base_c.as_str())],
            [HELPER.to_string()],
        )
        .expect("the unchanged retain helper must verify completely");
        assert!(!checked.is_empty());
        assert!(
            checked
                .iter()
                .all(|proof| proof.function_block.signature().name() == HELPER)
        );
    }
    let samples = sizes
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = retain_amid_unrelated_children_project(size);
            assert_eq!(c_source.matches(CALLER).count(), 1);
            assert_eq!(click_source.matches(CALLER).count(), 1);
            assert_eq!(&c_source[..c_source.find(CALLER).unwrap()], c_helper);
            assert_eq!(
                &click_source[..click_source.find(CALLER).unwrap()],
                click_helper
            );
            let (verified, sample) = scaling_sample(size, || {
                crate::surface::verify_c_sources_functions(
                    &click_source,
                    &[("retain.c", c_source.as_str())],
                    [CALLER.to_string()],
                )
            });
            let checked = verified.unwrap_or_else(|error| {
                panic!("{size}-unrelated fixture failed: {}", error.message())
            });
            assert!(!checked.is_empty());
            assert!(
                checked
                    .iter()
                    .all(|proof| proof.function_block.signature().name() == CALLER)
            );
            sample
        })
        .collect::<Vec<_>>();
    // Two overlapping geometric windows retain both scales. Increment bounds
    // remove fixed costs; at 4/8/16, 20/7 rejects a > k/16, the
    // former whole-proof 3x crossover at 16/32 without its fixed-cost slack.
    assert_near_linear_scaling_with_increment_bound(
        "a retain amid unrelated live children",
        &samples[..4],
    );
    assert_near_linear_scaling_with_increment_bound(
        "a retain amid many unrelated live children",
        &samples[1..],
    );
    samples
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: shared-child exit scaling with a calibrated finishing guard"]
fn a_retain_ignores_many_unrelated_live_children() {
    let samples = assert_retain_ignores_unrelated_live_children([1, 2, 4, 8, 16]);
    let samples = &samples[1..];
    let finishing = samples
        .iter()
        .map(|sample| {
            sample
                .named_work
                .get("operation `proof context finishing`")
                .copied()
                .unwrap_or(0)
        })
        .collect::<Vec<_>>();
    assert!(finishing.iter().all(|work| *work > 0), "{finishing:?}");
    // Differences remove fixed helper and entry costs. The old exit checker
    // looked linear under the whole-proof 3x guard. Its recorded
    // 4/8/16 finishing increments already expose the regression.
    let linear_increments = |work: &[usize]| {
        let (Some(earlier), Some(later)) = (
            work[work.len() - 2].checked_sub(work[work.len() - 3]),
            work[work.len() - 1].checked_sub(work[work.len() - 2]),
        ) else {
            return false;
        };
        // For B + k*N + a*N^2, 28/11 at 4/8/16 rejects
        // a > k/32, just as the former 20/7 at 8/16/32 did.
        later * 11 <= earlier * 28
    };
    assert!(
        linear_increments(&finishing),
        "finishing work: {finishing:?}"
    );
    // Recorded pre-fix curve from the owned-parameter exit-check regression
    // (871f90f68): this smaller fixture must still reject that failure.
    assert!(!linear_increments(&[6_100, 13_500, 35_000]));
}

/// A function owning `count` heap objects through its pointer parameters
/// and writing one cell of another.
fn owned_parameters_project(count: usize) -> (String, String) {
    let parameters = (0..count)
        .map(|index| format!(", struct child* other{index}"))
        .collect::<String>();
    let c_source = format!(
        "struct child {{\n    int32 refs;\n    int32 payload;\n}};\n\nvoid touch(struct child* obj{parameters}) {{\n    obj->refs = 1;\n}}\n"
    );
    let owned = (0..count)
        .map(|index| {
            format!(
                "    owns allocation(other{index}, sizeof(struct child));\n    owns *other{index};\n"
            )
        })
        .collect::<String>();
    let click_source = format!(
        "verifying \"touch.c\";\n\nvoid touch(struct child* obj{parameters}) {{\n    owns obj->refs;\n{owned}}} by {{\n    step();\n    step();\n    close();\n}}\n"
    );
    (c_source, click_source)
}

/// Owning more pointer parameters costs near-linear work: they share one
/// memory block, and no check pairs each of them with all the others.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3.1s in the parallel gate"]
fn owned_pointer_parameters_scale_with_their_number() {
    let samples = [1, 2, 4, 8]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = owned_parameters_project(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("touch.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!("{size}-parameter fixture failed: {}", error.message())
            });
            sample
        })
        .collect::<Vec<_>>();
    assert_near_linear_scaling("owned pointer parameters", &samples);
    let finishing = samples
        .iter()
        .map(|sample| {
            sample
                .named_work
                .get("operation `proof context finishing`")
                .copied()
                .unwrap_or(0)
        })
        .collect::<Vec<_>>();
    assert!(finishing.iter().all(|work| *work > 0), "{finishing:?}");
    let linear_increments = |work: &[usize]| {
        let (Some(earlier), Some(later)) =
            (work[1].checked_sub(work[0]), work[2].checked_sub(work[1]))
        else {
            return false;
        };
        later * 11 <= earlier * 28
    };
    // At 2/4/8, 28/11 removes fixed exit cost and rejects a > k/16,
    // the same crossover as the former 20/7 bound at 4/8/16.
    let whole = [samples[1].work, samples[2].work, samples[3].work];
    assert!(
        linear_increments(&whole),
        "owned-parameter total work increments: {samples:?}"
    );
    assert!(
        linear_increments(&finishing[1..]),
        "owned-parameter finishing increments: {finishing:?}"
    );
    // Recorded pre-fix finishing work at 4/8/16 in the owned-parameter
    // exit-check report closed by 871f90f68.
    // Keep the recorded larger-size curve as a negative control for the
    // same increment validator used by the measured smaller-size curve.
    assert!(!linear_increments(&[6_100, 13_500, 35_000]));
}

/// A selected field separation after unfold uses the live partition before
/// attempting to connect the older body compositions to surrounding owners.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.8s in the parallel gate"]
fn held_field_separation_precedes_general_composition_reasoning() {
    let mut work = Vec::new();
    for size in [4, 16] {
        let parameters = (0..size)
            .map(|i| format!(", struct node* q{i}"))
            .collect::<String>();
        let resources = (0..size)
            .map(|i| format!("consumes r{i}: cell(q{i});\n"))
            .collect::<String>();
        let unfolds = (0..size)
            .map(|i| format!("unfold(r{i});\n"))
            .collect::<String>();
        let c_source = format!(
            "struct node {{ uint64 word; struct node *left; struct node *right; }};
void inspect(struct node* parent, struct node* child{parameters}) {{ }}"
        );
        let click_source = format!(
            "verifying \"held.c\";
resource cell(p: struct node*) {{ field value: uint64; owns p->word; fact p->word == value; }}
void inspect(struct node* parent, struct node* child{parameters}) {{
 owns *parent; consumes c: cell(child); {resources}
}} by {{
 {unfolds}
 unfold(c);
 have separate(memory(parent->word), memory(child->word)) by close();
 step_until(function.exit); close();
}}"
        );
        let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
            verify_c_sources(&click_source, &[("held.c", &c_source)])
        });
        result.unwrap_or_else(|error| panic!("{size}: {}", error.message()));
        let selected = samples
            .iter()
            .filter(|sample| sample.tactic.tactic_name == "have")
            .collect::<Vec<_>>();
        assert_eq!(selected.len(), 1);
        work.push(selected[0].work);
    }
    assert!(work.iter().all(|count| *count > 0));
    assert!(
        work.windows(2).all(|pair| pair[0] == pair[1]),
        "held field lookup traversed unrelated compositions: {work:?}"
    );
}

/// Explicitly opening nested owners and borrowed projections must not search
/// every combination of unfolded definitions during exit certification.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.8s in the parallel gate"]
fn composite_borrow_partition_nested_openings_scale_with_depth() {
    let c = "struct node { int value; }; struct callbacks { void (*invoke)(void); }; void update(struct node *p, const struct callbacks *cb) { p->value = 1; cb->invoke(); }";
    let mut previous_work = None;
    let samples = [2usize, 4, 8, 16].map(|depth| {
        let mut source = String::from(r#"
verifying "callback.c";
contract void Callback() { ensures 1 == 1; }
resource node0(p: struct node*) { owns p->value; }
resource callbacks0(cb: const struct callbacks*) {
    views cb->invoke;
    fact Callback(cb->invoke);
}
"#);
        for layer in 1..=depth {
            let child = layer - 1;
            source.push_str(&format!("resource node{layer}(p: struct node*) {{ owns node{child}(p); }}\nresource callbacks{layer}(cb: const struct callbacks*) {{ owns callbacks{child}(cb); }}\n"));
        }
        source.push_str(&format!("void update(struct node* p, const struct callbacks* cb) {{ owns node{depth}(p); views callbacks{depth}(cb); ensures p->value == 1; }} by {{\n"));
        for layer in (1..=depth).rev() {
            source.push_str(&format!("unfold(node{layer}(p)); observe(callbacks{layer}(cb));\n"));
        }
        source.push_str(r#"
unfold(node0(p));
with(callbacks0(cb)) {
    have separate(memory(cb->invoke), memory(p->value));
    mark before;
    step();
    have separate(statement(0).footprint, memory(cb->invoke)) by {
        close() using { separate(memory(cb->invoke), memory(p->value)); };
    }
    have cb->invoke == at(before, cb->invoke) by {
        preserve(memory(cb->invoke), statement(0));
    }
    step_until(function.exit);
}
fold(node0(p));
"#);
        for layer in 1..=depth {
            source.push_str(&format!("fold(node{layer}(p));\n"));
        }
        source.push_str("close(); }");
        if depth == 2 {
            // Initialize shared frontend tables outside the scaling samples.
            verify_c_sources(&source, &[("callback.c", c)]).unwrap();
        }
        let verify = || verify_c_sources(&source, &[("callback.c", c)]);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            if let Some(previous) = previous_work {
                // Enforce the same growth law while running: a regression
                // should fail locally instead of exploring exponentially.
                crate::instrumentation::with_run_work_limit(3 * previous, verify)
            } else {
                verify()
            }
        });
        result.unwrap_or_else(|error| panic!("depth {depth}: {}", error.message()));
        previous_work = Some(work);
        (depth, work)
    });
    eprintln!("nested borrow partition work: {samples:?}");
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= 3 * pair[0].1,
            "superlinear nested openings: {samples:?}"
        );
    }
}

/// Guarded preparation visits one body; the complete rewrite also pays the
/// existing linear validation cost for surrounding owners.
///
/// Nightly: each of the four verifications costs over half a second in a
/// debug build at any size, and the proof's execution grows faster than
/// the owners (3,561, 6,045, 13,413 and 37,749 units at 4 to 32 owners in a
/// release build on 2026-10-15), so the largest size dominates.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 7.2s in the parallel gate"]
fn guarded_unfold_cell_preparation_scales_linearly_with_surrounding_owners() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/c_guarded_resource_disjoint_store.md");
    let markdown = std::fs::read_to_string(&path).unwrap();
    let input = crate::cli::parse_mdtest(&path, &markdown).unwrap();
    let mut work = Vec::new();
    for size in [4usize, 8, 16, 32, 64] {
        let parameters = (0..size)
            .map(|i| format!(", int32* q{i}"))
            .collect::<String>();
        let owners = (0..size)
            .map(|i| format!("owns q{i}[0..1];\n"))
            .collect::<String>();
        let source = input
            .click_source
            .as_ref()
            .unwrap()
            .replace(
                "struct cell* root)",
                &format!("struct cell* root{parameters})"),
            )
            .replace(
                "    requires root != 0;",
                &format!("{owners}    requires root != 0;"),
            );
        let c_source = input.c_sources[0].1.replace(
            "struct cell* root)",
            &format!("struct cell* root{parameters})"),
        );
        let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
            verify_c_sources(&source, &[("frame.c", &c_source)])
        });
        result.unwrap_or_else(|error| panic!("{size}: {}", error.message()));
        let selected = samples
            .iter()
            .filter(|sample| sample.tactic.tactic_name == "unfold")
            .collect::<Vec<_>>();
        assert_eq!(selected.len(), 1);
        work.push((size, selected[0].work));
    }
    assert!(work.iter().all(|&(_, count)| count > 0));
    // The selected unfold takes roughly six units per additional owner.
    // Bound the marginal work through each doubling of the surrounding frame.
    for pair in work.windows(2) {
        let added_owners = pair[1].0 - pair[0].0;
        let added_work = pair[1].1.saturating_sub(pair[0].1);
        assert!(
            added_work <= 7 * added_owners,
            "unfold work grew too quickly with surrounding owners: {work:?}"
        );
    }
}

/// Repeated checked increments must not rederive ranges through the entire
/// earlier expression chain. Measure the executed operations, not timings.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn signed_increment_overflow_checks_stay_flat_per_assignment() {
    let mut peaks = Vec::new();
    let mut totals = Vec::new();
    for size in [8, 16, 32, 64] {
        let mut c = String::from("int32 increment(int32 x0) {\n");
        for i in 1..=size {
            c.push_str(&format!("int32 x{i};\n"));
        }
        for i in 1..=size {
            c.push_str(&format!("x{i} = x{} + 1;\n", i - 1));
        }
        c.push_str(&format!("return x{size};\n}}"));
        let mut source = format!(
            "verifying \"increment.c\"; int32 increment(int32 x0) {{ requires x0 >= 0; requires x0 <= 1000000; ensures result == x0 + {size}; }} by {{\n"
        );
        source.push_str(&"step();\n".repeat(size * 2 + 1));
        source.push_str("close();\n}");
        let ((verified, work), events) = crate::instrumentation::collect(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                verify_c_sources(&source, &[("increment.c", c.as_str())])
            })
        });
        verified.unwrap_or_else(|error| panic!("size {size}: {}", error.message()));
        let steps = events
            .iter()
            .filter_map(|event| match event {
                crate::instrumentation::VerificationEvent::TacticFinished {
                    tactic, work, ..
                } if tactic.tactic_name == "step"
                    && tactic.source_index >= size
                    && tactic.source_index < size * 2 =>
                {
                    Some(*work)
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        assert!(steps.len() >= size);
        peaks.push(steps.iter().copied().max().unwrap());
        eprintln!(
            "increment size {size}: assignment peak {}, total work {work}",
            peaks.last().unwrap()
        );
        totals.push(ScalingSample {
            size,
            work,
            named_work: BTreeMap::new(),
        });
    }
    assert!(
        peaks.iter().all(|work| *work <= peaks[0] * 2),
        "increment step work must stay flat: {peaks:?}"
    );
    assert_near_linear_scaling_with_increment_bound("checked increment chains", &totals);
    let invalid = "verifying \"unbounded.c\"; int32 f(int32 x) { ensures result == x + 1; } by { step(); close(); }";
    assert!(
        verify_c_sources(
            invalid,
            &[("unbounded.c", "int32 f(int32 x) { return x + 1; }")]
        )
        .is_err(),
        "an unbounded increment still has an overflow path"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.3s in the parallel gate"]
fn unrelated_call_work_stays_flat_with_kept_pointer_aliases() {
    let mut calls = Vec::new();
    // Preserve the first-call baseline, largest alias population, and 7/5 bound.
    for size in [1, 32] {
        let parameters = (0..size)
            .map(|i| format!(", struct box* q{i}"))
            .collect::<String>();
        let sum = (0..size)
            .map(|i| format!("q{i}->v"))
            .collect::<Vec<_>>()
            .join(" + ");
        let c = format!(
            "struct box {{ int32 v; }}; void touch(int32* flags, int32* data, int32 k) {{ return; }} int32 caller(int32* flags, int32* data, int32 k, struct box* b{parameters}) {{ int32 total; b->v = 1; touch(flags, data, k); total = {sum}; return total; }}"
        );
        let requirements = (0..size)
            .map(|i| format!("requires q{i} == b;"))
            .collect::<String>();
        let source = format!(
            "verifying \"aliases.c\"; void touch(int32* flags, int32* data, int32 k) {{ owns flags[0..k]; owns data[0..k]; }} int32 caller(int32* flags, int32* data, int32 k, struct box* b{parameters}) {{ owns flags[0..k]; owns data[0..k]; owns *b; {requirements} ensures result == {size}; }} by {{ step(); step(); step(); step(); step(); close(); }}"
        );
        let (verified, events) = crate::instrumentation::collect(|| {
            verify_c_sources(&source, &[("aliases.c", c.as_str())])
        });
        verified.unwrap_or_else(|error| panic!("{size} aliases: {}", error.message()));
        let call = events
            .iter()
            .filter_map(|event| match event {
                crate::instrumentation::VerificationEvent::TacticFinished {
                    tactic, work, ..
                } if tactic.claim == "caller.contract"
                    && tactic.tactic_name == "step"
                    && tactic.source_index == 2 =>
                {
                    Some(*work)
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(call.len(), 1, "one selected call step at size {size}");
        calls.push(call[0]);
    }
    eprintln!("unrelated call work by alias count: {calls:?}");
    assert!(
        calls.iter().all(|work| *work * 5 <= calls[0] * 7),
        "call work grew with irrelevant aliases: {calls:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn symbolic_index_store_work_is_flat_across_recorded_order_chains() {
    let mut peaks = Vec::new();
    let mut totals = Vec::new();
    for size in [4, 8, 16, 32] {
        let parameters = (0..=size)
            .map(|i| format!(", int32 x{i}"))
            .collect::<String>();
        let stores = (1..=size)
            .map(|i| format!("data[x{i}] = {i};"))
            .collect::<String>();
        let c = format!(
            "int32 caller(int32* data, int32 len{parameters}) {{ int32 first; data[x0] = 100; {stores} first = data[x0]; return first; }}"
        );
        let requirements = (0..size)
            .map(|i| format!("requires x{i} < x{};", i + 1))
            .collect::<String>();
        let steps = "step();".repeat(size + 4);
        let source = format!(
            "verifying \"ordered.c\"; int32 caller(int32* data, int32 len{parameters}) {{ owns data[0..len]; requires 0 <= x0; {requirements} requires x{size} < len; ensures result == 100; }} by {{ {steps} close(); }}"
        );
        let ((verified, work), events) = crate::instrumentation::collect(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                verify_c_sources(&source, &[("ordered.c", c.as_str())])
            })
        });
        verified.unwrap_or_else(|error| panic!("size {size}: {}", error.message()));
        let peak = events
            .iter()
            .filter_map(|event| match event {
                crate::instrumentation::VerificationEvent::TacticFinished {
                    tactic, work, ..
                } if tactic.tactic_name == "step"
                    && tactic.source_index >= 1
                    && tactic.source_index <= size + 1 =>
                {
                    Some(*work)
                }
                _ => None,
            })
            .max()
            .unwrap();
        peaks.push(peak);
        totals.push(ScalingSample {
            size,
            work,
            named_work: BTreeMap::new(),
        });
    }
    eprintln!("ordered store peaks: {peaks:?}");
    assert!(
        peaks.iter().all(|work| *work * 2 <= peaks[0] * 3),
        "{peaks:?}"
    );
    assert_near_linear_scaling_with_increment_bound("symbolic ordered stores", &totals);
}

/// Owns seed every input field before the first store. This catches both the
/// initial index cost leaking into a step and repeated visits to other objects.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: twelve full-source proofs with single and repeated calls"]
fn owned_parameter_field_store_work_is_flat() {
    let mut peaks = Vec::new();
    let mut calls = Vec::new();
    for (linked, repeated) in [(false, false), (true, false), (false, true), (true, true)] {
        for size in [4usize, 16, 32] {
            let count = size + usize::from(linked);
            let kind = if linked { "node" } else { "box" };
            let layout = if linked {
                "struct node { struct node* next; int32 v; };"
            } else {
                "struct box { int32 v; };"
            };
            let parameters = (0..count)
                .map(|i| format!(", struct {kind}* p{i}"))
                .collect::<String>();
            let owns = (0..count)
                .map(|i| format!("owns *p{i};\n"))
                .collect::<String>();
            let stores = (0..size)
                .map(|i| {
                    if linked {
                        format!("p{i}->next = p{};\n", i + 1)
                    } else {
                        format!("p{i}->v = {i};\n")
                    }
                })
                .collect::<String>();
            let (last_store, read, expected) = if linked {
                (
                    format!("p{size}->v = 9;\n"),
                    format!("p0{}->v", "->next".repeat(size)),
                    9,
                )
            } else {
                (
                    String::new(),
                    (0..size)
                        .map(|i| format!("p{i}->v"))
                        .collect::<Vec<_>>()
                        .join(" + "),
                    (size * (size - 1) / 2) as i32,
                )
            };
            let signature = format!("int32 caller(int32* flags, int32* data, int32 k{parameters})");
            let call_count = if repeated { size } else { 1 };
            let call_source = "touch(flags, data, k);\n".repeat(call_count);
            let c = format!(
                "{layout}
void touch(int32* flags, int32* data, int32 k) {{ return; }}
{signature} {{ int32 total; {stores}{last_store}
{call_source} total = {read}; return total; }}"
            );
            let source = format!(
                "verifying \"fields.c\";
void touch(int32* flags, int32* data, int32 k) {{
owns flags[0..k]; owns data[0..k];
}}
{signature} {{ owns flags[0..k]; owns data[0..k]; {owns}
ensures result == {expected};
}} by {{ {} close(); }}",
                "step();\n".repeat(size + usize::from(linked) + 3 + call_count)
            );
            let ((result, samples), events) = crate::instrumentation::collect(|| {
                crate::instrumentation::collect_tactic_work(|| {
                    verify_c_sources(&source, &[("fields.c", c.as_str())])
                })
            });
            result.unwrap_or_else(|error| {
                panic!("linked={linked}, size={size}: {}", error.message())
            });
            let call_work: Vec<_> = samples
                .iter()
                .filter(|sample| sample.tactic.tactic_name == "step")
                .skip(1 + size + usize::from(linked))
                .take(call_count)
                .map(|sample| sample.work)
                .collect();
            assert_eq!(call_work.len(), call_count);
            calls.push((linked, size, *call_work.iter().max().unwrap()));
            let steps: Vec<_> = samples
                .iter()
                .filter(|sample| sample.tactic.tactic_name == "step")
                .skip(1)
                .take(size + usize::from(linked))
                .map(|sample| sample.work)
                .collect();
            assert_eq!(steps.len(), size + usize::from(linked));
            let call_micros: Vec<_> = events
                .iter()
                .filter_map(|event| match event {
                    crate::instrumentation::VerificationEvent::TacticFinished {
                        tactic,
                        elapsed,
                        ..
                    } if tactic.tactic_name == "step" => Some(elapsed.as_micros()),
                    _ => None,
                })
                .skip(1 + size + usize::from(linked))
                .take(call_count)
                .collect();
            eprintln!(
                "calls linked={linked} repeated={repeated} N={size}: work {call_work:?}, time {call_micros:?}us"
            );
            let mut micros: Vec<_> = events
                .iter()
                .filter_map(|event| match event {
                    crate::instrumentation::VerificationEvent::TacticFinished {
                        tactic,
                        elapsed,
                        ..
                    } if tactic.tactic_name == "step" => Some(elapsed.as_micros()),
                    _ => None,
                })
                .skip(1)
                .take(size + usize::from(linked))
                .collect();
            micros.sort_unstable();
            eprintln!(
                "field stores linked={linked} N={size}: median {}us, max {}us",
                micros[micros.len() / 2],
                micros.last().unwrap()
            );
            peaks.push((linked, size, *steps.iter().max().unwrap()));
        }
    }
    eprintln!("owned parameter field stores: {peaks:?}");
    for family in peaks.chunks(3) {
        assert!(
            family.iter().all(|(_, _, work)| *work <= family[0].2 + 32),
            "a field store visited unrelated owned objects: {peaks:?}"
        );
    }
    eprintln!("calls beside owned parameters: {calls:?}");
    // The cold index may switch from walking a tiny merge prefix to
    // building the fixed-size contract directly. Allow that fixed setup
    // difference; the separate cold-index regression grows history to 256.
    for family in calls.chunks(3) {
        assert!(
            family.iter().all(|(_, _, work)| *work <= family[0].2 + 32),
            "a call visited unrelated owned objects: {calls:?}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn exact_fact_lookup_does_not_reconstruct_unrelated_integer_facts() {
    let mut work = Vec::new();
    let sizes = [8usize, 16, 32];
    for size in sizes {
        let (_, mut source) = function_with_unrelated_facts(
            size,
            "    step();\n    have target == 7 by close();\n    step_until(function.exit);\n    close();\n",
        );
        // Keep the lookup at a live statement frontier. A return would enter
        // the distinct post-execution premise-search path.
        let c = "int32 exact_fact_target(int32 target) { int32 copy = target; return copy; }";
        for index in 0..size {
            source = source.replace(
                &format!("requires target != {};", index + 100),
                &format!("requires to_integer(target) != {};", index + 100),
            );
        }
        let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
            verify_c_sources(&source, &[("exact_fact_target.c", c)])
        });
        result.unwrap_or_else(|error| panic!("{size}: {}", error.message()));
        let selected = samples
            .iter()
            .filter(|sample| sample.tactic.tactic_name == "have")
            .collect::<Vec<_>>();
        assert_eq!(selected.len(), 1);
        assert!(!selected[0].failed);
        work.push(selected[0].work);
    }
    assert!(work.iter().all(|count| *count > 0));
    assert!(
        work.windows(2).all(|pair| pair[1] <= pair[0] * 2),
        "exact fact lookup must not reconstruct an ambient fact per input: {work:?}"
    );
    let indexed = |costs: &[usize]| costs.iter().all(|work| *work <= costs[0] + 16);
    eprintln!("exact fact lookup work: {work:?}");
    assert!(indexed(&work), "{work:?}");
    let rebuilt = work
        .iter()
        .zip(sizes)
        .map(|(work, size)| work + size)
        .collect::<Vec<_>>();
    assert!(
        !indexed(&rebuilt),
        "the smaller fixture must detect a visit per unrelated fact: {work:?}"
    );
}

/// Branches that call through a pointer-field resource retain their statement
/// effect records beside unrelated caller facts, rather than reconstructing
/// the call's internal memory chain at the join.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: four modular pointer-field branch joins"]
fn pointer_field_call_branch_join_scales_with_unrelated_caller_facts() {
    let path = std::path::Path::new("c_pointer_field_preserving_calls_join_branches.md");
    let fixture = crate::cli::parse_mdtest(
        path,
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/mdtests/c_pointer_field_preserving_calls_join_branches.md"
        )),
    )
    .unwrap();
    let source = fixture.click_source.unwrap();
    let c_source = &fixture.c_sources[0].1;
    const CALLER: &str = "vector_replace_if";
    // The helpers never call the changing entry point. Check their complete
    // implementations once; every sample below cold-checks the entire caller.
    assert_eq!(source.matches(CALLER).count(), 1);
    assert_eq!(c_source.matches(CALLER).count(), 1);
    let source_helpers = &source[..source.find(CALLER).unwrap()];
    let c_helpers = &c_source[..c_source.find(CALLER).unwrap()];
    {
        let helpers = crate::surface::verify_c_sources_functions(
            &source,
            &[("vector.c", c_source.as_str())],
            ["vector_get".to_string(), "vector_set".to_string()],
        )
        .expect("both unchanged helper implementations must verify");
        for name in ["vector_get", "vector_set"] {
            assert!(
                helpers
                    .iter()
                    .any(|proof| proof.function_block.signature().name() == name)
            );
        }
        assert!(helpers.iter().all(|proof| matches!(
            proof.function_block.signature().name(),
            "vector_get" | "vector_set"
        )));
    }
    let mut samples = Vec::new();
    for size in [8, 16, 32, 64] {
        let parameters = (0..size)
            .map(|index| format!(", int32 noise_{index}"))
            .collect::<String>();
        let requirements = (0..size)
            .map(|index| format!("    requires 0 <= noise_{index};\n"))
            .collect::<String>();
        let signature = "int32 replace\n)";
        assert_eq!(source.matches(signature).count(), 1);
        assert_eq!(c_source.matches(signature).count(), 1);
        let signature = format!("int32 replace{parameters}\n)");
        let c_source = c_source.replace("int32 replace\n)", &signature);
        let source = source.replace("int32 replace\n)", &signature);
        let start = source.find("int32 vector_replace_if(").unwrap();
        let source = format!(
            "{}{}",
            &source[..start],
            source[start..].replacen(
                "    requires 0 <= index;",
                &format!("{requirements}    requires 0 <= index;"),
                1,
            )
        );
        assert_eq!(&source[..source.find(CALLER).unwrap()], source_helpers);
        assert_eq!(&c_source[..c_source.find(CALLER).unwrap()], c_helpers);
        let (result, sample) = scaling_sample(size, || {
            crate::surface::verify_c_sources_functions(
                &source,
                &[("vector.c", c_source.as_str())],
                [CALLER.to_string()],
            )
        });
        let checked = result.unwrap_or_else(|error| panic!("size {size}: {}", error.message()));
        assert!(!checked.is_empty(), "the complete caller must be checked");
        assert!(
            checked
                .iter()
                .all(|proof| proof.function_block.signature().name() == CALLER)
        );
        samples.push(sample);
    }
    assert_near_linear_scaling("pointer-field call branch join", &samples);
    // For B + k*N + a*N^2, 28/11 on increments at 16/32/64
    // rejects a > k/128, just as 20/7 at 32/64/128 did.
    // Fixed whole-proof costs cannot hide quadratic join work.
    let earlier = samples[2].work.checked_sub(samples[1].work);
    let later = samples[3].work.checked_sub(samples[2].work);
    assert!(
        matches!((earlier, later), (Some(earlier), Some(later)) if later * 11 <= earlier * 28),
        "pointer-field join work increments must remain near linear: {samples:?}"
    );
}

/// A proof `if` at an execution frontier lowers its condition against the
/// branch's indexed fact context, so the split costs its condition and not
/// the proof facts written before it.
///
/// Each arm used to copy the branch's facts into a list and lower the
/// condition against a context rebuilt from that whole list, so every split
/// assumed every earlier fact again: the loop body of
/// `examples/rbtree/rbtree-erase/rbtree_erase_color_flips_red_all.click` paid about
/// 185,000 control units for it. The test holds one loop-body split fixed
/// beside 1 to 8 earlier `have` facts and pins the context entries the split
/// adds
/// (`context_rebuild_entries` with the split minus without it).
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: proof-if context scaling compares eight complete loop proofs"]
fn proof_if_split_ignores_earlier_unrelated_facts() {
    fn rebuild_entries(size: usize, split: bool) -> usize {
        // Establish the shared lower bound once; each distinct earlier fact
        // then needs one explicit transitivity application instead of a new
        // arithmetic search. Keep i symbolic so these remain distinct facts.
        let haves = (1..=size)
            .map(|k| {
                format!(
                    "            have i >= 0 - {k} by {{\n\
                     \x20               apply(click::integer::le_transitive(0 - {k}, 0, to_integer(i)));\n            }}\n"
                )
            })
            .collect::<String>();
        // Arms that each close the iteration have no continuation to rejoin,
        // so the split is taken rather than tried as a straight-line join.
        let close = if split {
            "            if flag == i {\n                have flag == i by close();\n            \
             } else {\n                have not (flag == i) by close();\n            \
             }\n"
        } else {
            ""
        };
        let click_source = format!(
            r#"verifying "split.c";
int32 count_once(int32 flag) {{
    ensures result == 1;
}} by {{
    step();
    step();
    loop {{
        decreases 1 - i;
        invariant i >= 0;
        invariant i <= 1;
        initialize by {{ close(); }}
        maintain by {{
            mark before_increment;
            step();
            have 0 <= to_integer(i) by {{
                close() using {{
                    at(before_increment, i) >= 0;
                    at(before_increment, i) <= 1;
                }};
            }}
{haves}{close}        }}
    }}
    step();
    close();
}}
"#
        );
        let c_source = "int32 count_once(int32 flag) {\n    int32 i;\n    i = 0;\n    \
                        while (i < 1) { i = i + 1; }\n    return i;\n}\n";
        let before = crate::kernel::reasoning::path_facts::context_rebuild_entries();
        verify_c_sources(&click_source, &[("split.c", c_source)]).unwrap_or_else(|error| {
            panic!("size {size} split={split} failed: {}", error.message())
        });
        crate::kernel::reasoning::path_facts::context_rebuild_entries() - before
    }
    let added = [1, 2, 4, 8]
        .map(|size| rebuild_entries(size, true).saturating_sub(rebuild_entries(size, false)));
    eprintln!("context entries a proof `if` adds beside 1/2/4/8 facts: {added:?}");
    // The split's own entries do not depend on the earlier facts. Rebuilding
    // the branch's facts per arm added at least two entries per fact.
    assert!(
        added.iter().all(|entries| *entries == added[0]),
        "a proof `if` rebuilds context entries for earlier unrelated facts: {added:?}"
    );
}

/// A failing bare transport cites only its source and rebuilds no context per
/// ambient fact.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn failing_bare_transport_reuses_candidate_assumptions() {
    use crate::instrumentation::collect;
    let mut samples = Vec::new();
    for size in [4, 16, 64] {
        let requirements = (0..size)
            .map(|i| format!("requires extra != {i};\n"))
            .collect::<String>();
        let source = format!(
            r#"verifying "fill.c"; void fill(uint8* dst, int32 extra) {{ owns dst[0..4]; {requirements} }} by {{
step(); mark filled; step();
transport(at(filled, dst[0]) == 7, dst[0] == 7);
}}"#
        );
        let before = crate::kernel::reasoning::path_facts::context_rebuild_entries();
        let (result, _) = collect(|| {
            verify_c_sources(
                &source,
                &[(
                    "fill.c",
                    "void fill(uint8* dst, int32 extra) { dst[0] = 7; dst[0] = 0; }",
                )],
            )
        });
        let entries = crate::kernel::reasoning::path_facts::context_rebuild_entries() - before;
        let error = result.expect_err("overwritten value cannot be transported");
        assert!(
            !error.message().contains("budget exhausted"),
            "{}",
            error.message()
        );
        samples.push((size, entries));
    }
    eprintln!("bare transport context rebuilds: {samples:?}");
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 5,
            "repeated ambient rebuilds: {samples:?}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.8s in the parallel gate"]
fn branch_view_entry_loadability_ignores_prior_effects() {
    for slot in [0, 2] {
        let contract = if slot == 0 {
            "owns p[0..1];"
        } else {
            "views p[0..1]; owns p[2..3];"
        };
        let mut samples = Vec::new();
        for size in [4, 16, 64] {
            let stores = (0..size)
                .map(|value| format!("p[{slot}] = {value};\n"))
                .collect::<String>();
            let steps = "step();\n".repeat(size + 3);
            let program = format!(
                "int32 original_value(int32* p, int32 flag) {{
                    int32 original = p[0];
                    int32 selected;
                    {stores}
                    if (flag < 0) {{ selected = original; }} else {{ selected = original; }}
                    return selected;
                }}"
            );
            let proof = format!(
                r#"verifying "entry_view.c";
                int32 original_value(int32* p, int32 flag) {{
                    {contract}
                    ensures result == old(p[0]);
                }} by {{
                    {steps}
                    branch ensuring {{
                        views p[0..1];
                        fact selected == old(p[0]);
                    }} {{
                        true => {{ step(); }}
                        false => {{ step(); }}
                    }}
                    step();
                    close();
                }}"#
            );
            let (result, sample) = scaling_sample(size, || {
                verify_c_sources(&proof, &[("entry_view.c", &program)])
            });
            result.unwrap_or_else(|error| panic!("{}", error.message()));
            let work = sample.named_work["operation `branch interface entry loadability`"];
            assert!(work > 0, "the interface must check the entry view");
            samples.push((size, work));
        }
        assert!(
            samples.iter().all(|(_, work)| *work == samples[0].1),
            "changing the length of the store history at slot {slot} changed entry-loadability work: {samples:?}",
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5.2s in the parallel gate"]
fn named_unfold_constructs_the_selected_arm_once() {
    use crate::instrumentation::{VerificationEvent, collect};

    let c = "int32 read_cell(int32* p, int32 x) { return p[0]; }";
    let sample = |body: usize, frame: usize| {
        let owners = |count: usize, start: usize| {
            (0..count)
                .map(|i| {
                    let slot = start + 2 * i;
                    format!("owns p[{slot}..{}];\n", slot + 1)
                })
                .collect::<String>()
        };
        let arm_owners = owners(body, 0);
        let frame_owners = owners(frame, 128);
        let proof = format!(
            r#"verifying "read_cell.c";
            spec enum Model {{ Empty, Full(int32), }}
            resource cell_at(p: int32*) {{
                field model: Model;
                match model {{
                    Model::Empty => {{ fact p == 0; }},
                    Model::Full(value) => {{
                        {arm_owners}
                        fact p[0] == value;
                    }},
                }}
            }}
            int32 read_cell(int32* p, int32 x) {{
                consumes held: cell_at(p);
                requires held.model == Model::Full(x);
                {frame_owners}
                ensures result == x;
            }} by {{
                unfold(held);
                step();
                close();
            }}"#
        );
        let (verified, events) = collect(|| verify_c_sources(&proof, &[("read_cell.c", c)]));
        verified.unwrap_or_else(|error| panic!("body {body}, frame {frame}: {}", error.message()));
        let mut in_unfold = false;
        let mut arm_checks = 0;
        for event in events {
            match event {
                VerificationEvent::TacticStarted(tactic) if tactic.tactic_name == "unfold" => {
                    in_unfold = true;
                }
                VerificationEvent::OperationFinished { name, .. }
                    if in_unfold && name == "instance arm refutations" =>
                {
                    arm_checks += 1;
                }
                VerificationEvent::TacticFinished { tactic, work, .. }
                    if tactic.tactic_name == "unfold" =>
                {
                    assert_eq!(arm_checks, 1, "body {body}, frame {frame}");
                    return work;
                }
                _ => {}
            }
        }
        panic!("expected an explicit unfold");
    };
    let frame_work = [4, 16, 64].map(|frame| sample(1, frame));
    assert!(
        frame_work.iter().all(|work| *work <= frame_work[0] + 32),
        "a fixed arm must ignore the unrelated frame: {frame_work:?}"
    );
    for body in [4, 8, 16] {
        assert!(sample(body, 0) > 0);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 11s in the parallel gate"]
fn scalar_read_after_branch_ignores_other_slots_on_its_line() {
    use crate::instrumentation::{VerificationEvent, collect};

    let c = "int32 bump(int32* p, int32 x) {
        int32 scratch;
        if (x >= 0) { p[0] = x; } else { p[0] = 0; }
        p[0] = p[0] + 1;
        return p[0];
    }";
    let samples = [4, 16, 64].map(|size| {
        let owners = (1..=size)
            .map(|i| format!("owns p[{}..{}];\n", 2 * i, 2 * i + 1))
            .collect::<String>();
        let proof = format!(
            r#"verifying "bump.c";
            int32 bump(int32* p, int32 x) {{
                requires x < 2147483647;
                owns p[0..1];
                {owners}
                ensures result > 0 by {{
                    step();
                    branch ensuring {{
                        fact p[0] >= 0;
                        fact p[0] < 2147483647;
                        owns p[0..1];
                    }} {{
                        true => {{ step(); }}
                        false => {{ step(); }}
                    }}
                    step();
                    step();
                    close();
                }}
            }}"#
        );
        let (verified, events) = collect(|| verify_c_sources(&proof, &[("bump.c", c)]));
        verified.unwrap_or_else(|error| panic!("{size}: {}", error.message()));
        let increment = |tactic: &crate::instrumentation::TacticEvent| {
            tactic.tactic_name == "step" && tactic.statement_index == 4
        };
        let mut in_increment = false;
        let mut scans = Vec::new();
        for event in events {
            match event {
                VerificationEvent::TacticStarted(tactic) if increment(&tactic) => {
                    in_increment = true;
                }
                VerificationEvent::TacticFinished { tactic, .. } if increment(&tactic) => {
                    break;
                }
                VerificationEvent::OperationFinished { name, work, .. } if in_increment => {
                    assert_ne!(name, "memory load: distinct-cell reduction");
                    if name == "memory load: equal-cell scan" {
                        scans.push(work);
                    }
                }
                _ => {}
            }
        }
        assert!(in_increment, "the explicit increment step must run");
        scans
    });
    assert_eq!(
        samples[0].len(),
        1,
        "the increment must read the joined cell"
    );
    assert!(
        samples[0][0] <= 16 && samples.iter().all(|sample| *sample == samples[0]),
        "the read must seek past disjoint same-line slots: {samples:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4.3s in the parallel gate"]
fn branch_interface_fact_publication_extends_one_indexed_context() {
    let c_source = "struct cell { int32 value; }; int32 bump(struct cell* p, int32 x, int32 flag) { p->value = flag; return 0; }";
    let mut samples = Vec::new();
    for size in [16usize, 32, 64, 128] {
        let exported = (1..=size)
            .map(|i| format!("fact x <= {i};\n"))
            .collect::<String>();
        let required = exported.replace("fact", "requires");
        let click_source = format!(
            r#"
            verifying "joins.c";
            resource slot(p: struct cell*) {{ field model: int32; owns p->value; fact p->value == model; }}
            int32 bump(struct cell* p, int32 x, int32 flag) {{
                requires p != 0; {required} owns c: slot(p); ensures result == 0;
            }} by {{
                if flag == 0 ensuring {{ owns c: slot(p); {exported} }} then {{
                    unfold(c); step(); let c = fold(slot(p), {{ model: 0 }});
                }} else {{
                    unfold(c); step(); let c = fold(slot(p), {{ model: flag }});
                }}
                step(); close();
            }}
        "#
        );
        let (verified, sample) = scaling_sample(size, || {
            verify_c_sources(&click_source, &[("joins.c", c_source)])
        });
        verified.unwrap_or_else(|error| panic!("{}", error.message()));
        samples.push(sample);
    }
    assert_near_linear_scaling("branch interface exported facts", &samples);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3.0s in the parallel gate"]
fn branch_checking_ignores_unused_parameters_and_premises() {
    for grow_parameters in [false, true] {
        let mut samples = Vec::new();
        for size in [4, 16, 64] {
            let (parameters, premises) = if grow_parameters {
                (
                    (0..size).map(|i| format!(", int32 unused{i}")).collect(),
                    String::new(),
                )
            } else {
                (
                    String::new(),
                    (1..=size)
                        .map(|i| format!("requires x != -{i};\n"))
                        .collect(),
                )
            };
            let program = format!(
                "int32 bounded(int32 x{parameters}) {{
                    int32 y;
                    if (x >= 0) {{ y = x; }} else {{ y = 0; }}
                    return y + 1;
                }}"
            );
            let proof = format!(
                r#"verifying "branch.c";
                int32 bounded(int32 x{parameters}) {{
                    requires x < 2147483647;
                    {premises}
                    ensures result > 0 by {{
                        step();
                        branch ensuring {{
                            fact y >= 0;
                            fact y < 2147483647;
                        }} {{
                            true => {{ step(); }}
                            false => {{ step(); }}
                        }}
                        step();
                        close();
                    }}
                }}"#
            );
            let (result, sample) =
                scaling_sample(size, || verify_c_sources(&proof, &[("branch.c", &program)]));
            result.unwrap_or_else(|error| panic!("{}", error.message()));
            let operation = if grow_parameters {
                "operation `branch interface fact lowering`"
            } else {
                "operation `C condition theorem construction`"
            };
            let work = sample.named_work[operation];
            assert!(work > 0, "{operation} should run");
            samples.push((size, work));
        }
        assert!(
            samples.iter().all(|(_, work)| *work == samples[0].1),
            "branch checking work grew with extra {}: {samples:?}",
            if grow_parameters {
                "parameters"
            } else {
                "premises"
            },
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn mixed_width_owned_entry_work_is_independent_of_segment_length() {
    let program = "void entry(unsigned long *word, unsigned char *bytes) {}";
    verify_c_sources("theorem warm() { ensures true by close(); }", &[]).unwrap();
    let mut baseline = None;
    for length in [32, 1_024, 65_536, 2_147_483_647] {
        let source = format!(
            "verifying \"entry.c\"; void entry(uint64* word, uint8* bytes) {{ owns word[0..1]; owns bytes[0..{length}]; }}"
        );
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            verify_c_sources(&source, &[("entry.c", program)])
        });
        result.expect("the original empty function must verify at every byte length");
        assert_eq!(
            work,
            *baseline.get_or_insert(work),
            "length {length}: full entry work depends on numeric length"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn native_read_equality_refusal_does_not_restart_state_search_as_integer() {
    let c = "int32 read_after_store(int32 *a, int32 k) { a[3] = 5; return a[k]; }";
    verify_c_sources(
        "verifying \"read.c\"; int32 read_after_store(int32 *a, int32 k) {
            owns a[0..16]; requires 0 <= k; requires k < 16;
            ensures result == a[k]; }",
        &[("read.c", c)],
    )
    .expect("warm-up verifies");
    // Integer arithmetic must still establish native equality for each
    // signed and unsigned 32-bit carrier, without a native equality input.
    for ty in ["int32", "uint32"] {
        let c = format!("{ty} pick({ty} x, {ty} y) {{ return x; }}");
        let source = format!(
            "import click::integer; verifying \"integer_input.c\";
             {ty} pick({ty} x, {ty} y) {{
               requires to_integer(x) + 1 == to_integer(y) + 1;
               ensures result == y;
             }}"
        );
        verify_c_sources(&source, &[("integer_input.c", c.as_str())]).unwrap_or_else(|error| {
            panic!(
                "{ty} Integer-to-native equality control: {}",
                error.message()
            )
        });
    }
    for length in [4usize, 16, 64] {
        let source = format!(
            "verifying \"read.c\";
             resource block(p: int32*) {{ owns p[0..{length}]; }}
             int32 read_after_store(int32 *a, int32 k) {{
               owns block(a); requires 0 <= k; requires k < {length};
               ensures result == old(a[k]);
             }} by {{ unfold(block(a)); step_until(function.exit); fold(block(a)); close(); }}"
        );
        let (result, events) =
            crate::instrumentation::collect(|| verify_c_sources(&source, &[("read.c", c)]));
        let error = result.expect_err("the read may alias the changed cell");
        assert!(
            error
                .message()
                .contains("the store to `a[3]` may have written"),
            "{}",
            error.message()
        );
        let frame_searches = events
            .iter()
            .filter(|event| {
                matches!(event,
                    crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                        if *name == "solve closure: state transport"
                )
            })
            .count();
        assert!(
            frame_searches <= 1,
            "size {length}: the native refusal restarted frame search {frame_searches} times through Integer goals"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.164s for composite read refusal across three array sizes"]
fn composite_native_read_equality_refusal_keeps_one_state_search() {
    let c = "int32 read_after_store(int32 *a, int32 k) { a[3] = 5; return a[k]; }";
    for length in [4usize, 8, 16] {
        let source = format!(
            "verifying \"read.c\";
             resource block(p: int32*) {{ owns p[0..{length}]; }}
             int32 read_after_store(int32 *a, int32 k) {{
               owns block(a); requires 0 <= k; requires k < {length};
               ensures result + 0 == old(a[k]) + 0;
             }} by {{ unfold(block(a)); step_until(function.exit); fold(block(a)); close(); }}"
        );
        let (result, events) =
            crate::instrumentation::collect(|| verify_c_sources(&source, &[("read.c", c)]));
        let error = result.expect_err("zero offsets cannot hide a potentially changed read");
        assert!(!error.message().contains("budget exhausted"), "{error}");
        let searches = events
            .iter()
            .filter(|event| {
                matches!(event,
                    crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                        if *name == "solve closure: state transport"
                )
            })
            .count();
        assert!(
            searches <= 1,
            "size {length}: arithmetic restarted state search {searches} times"
        );
    }
}

/// A loop-free function that stores before each of `returns` early returns.
/// Path `k` shares the checked prefix of every earlier path.
pub(super) fn early_return_project(returns: usize) -> (String, String) {
    let mut c = String::from("int32 mark(int32 *a, int32 x) {\n");
    for index in 0..returns {
        c.push_str(&format!(
            "    a[{index}] = {index};\n    if (x == {index}) {{ return 1; }}\n"
        ));
    }
    c.push_str("    return 0;\n}\n");
    let click = format!(
        "verifying \"mark.c\";\nint32 mark(int32 *a, int32 x) {{\n    owns a[0..{returns}];\n    ensures result >= 0;\n}}\n"
    );
    (click, c)
}

/// Completing each early-return path borrows its retained trace. The traces
/// share their prefixes; copying each one made completion quadratic. With no
/// storage write on any path, the storage footprint check builds no path
/// context: it cost each path its whole fact history (231, 567 and 1623
/// units here) to find nothing to check.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn completing_early_return_paths_borrows_their_shared_traces() {
    let copies = [4, 8, 16].map(|returns| {
        let (click, c) = early_return_project(returns);
        let ((verified, copies), sample) = scaling_sample(returns, || {
            crate::kernel::proof::measure_sequence_copies(|| {
                verify_c_sources(&click, &[("mark.c", c.as_str())])
            })
        });
        verified.unwrap_or_else(|error| panic!("{returns} returns: {}", error.message()));
        assert_eq!(
            sample
                .named_work
                .get("operation `storage write footprint check`")
                .copied()
                .unwrap_or(0),
            0,
            "{returns} returns: a path without storage writes built a footprint context"
        );
        copies
    });
    assert!(
        copies.windows(2).all(|pair| pair[1] * 2 <= pair[0] * 5),
        "path completion copied its shared traces: {copies:?}"
    );
}

/// The deepest brace nesting in `source`.
fn brace_depth(source: &str) -> usize {
    let mut depth = 0usize;
    let mut deepest = 0;
    for character in source.chars() {
        match character {
            '{' => {
                depth += 1;
                deepest = deepest.max(depth);
            }
            '}' => depth = depth.saturating_sub(1),
            _ => {}
        }
    }
    deepest
}

/// Expands the grouped proof of [`early_return_project`] and checks the
/// expansion again from its text, on a thread with the fixture stack.
fn expanded_early_return_proof(returns: usize) -> (String, String) {
    let (click, c) = early_return_project(returns);
    let verified = verify_c_sources(&click, &[("mark.c", c.as_str())])
        .unwrap_or_else(|error| panic!("{returns} returns: {}", error.message()));
    let expanded = expand_checked_grouped_claim(&click, &verified, "mark")
        .unwrap_or_else(|error| panic!("{returns} returns expand: {}", error.message()));
    (expanded, c)
}

/// Sequential early returns expand one after another rather than each inside
/// the previous `else` arm, so the expansion's nesting is independent of how
/// many returns the function has. The terminal joins that check the expanded
/// proof republish each arm's paths without merging any path's facts into a
/// fresh stream: a deeper path is republished at every enclosing join, and
/// copying its history there made checking the expansion cubic.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.8s in the parallel gate"]
fn early_return_expansions_stay_flat_and_join_without_copying_paths() {
    std::thread::Builder::new()
        .name("early-return-expansion".into())
        .stack_size(64 << 20)
        .spawn(|| {
            let mut depths = Vec::new();
            for returns in [2, 4, 8] {
                let (expanded, c) = expanded_early_return_proof(returns);
                depths.push(brace_depth(&expanded));
                crate::surface::proof::take_terminal_join_materialized_facts();
                crate::surface::proof::without_implicit_solve(|| {
                    verify_c_sources(&expanded, &[("mark.c", c.as_str())])
                })
                .unwrap_or_else(|error| panic!("{returns} returns reverify: {}", error.message()));
                assert_eq!(
                    crate::surface::proof::take_terminal_join_materialized_facts(),
                    0,
                    "{returns} returns: a terminal join copied its arms' path facts"
                );
            }
            assert!(
                depths.iter().all(|depth| *depth == depths[0]),
                "expanded early returns nest with their count: {depths:?}"
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

/// At 128 returns the nested expansion exceeded the parser's delimiter
/// depth of 128 and the expansion was refused, though the proof verified.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 63s in a debug build to expand and re-verify 128 early returns"]
fn one_hundred_twenty_eight_early_returns_expand_and_reverify() {
    std::thread::Builder::new()
        .name("early-return-expansion-128".into())
        .stack_size(64 << 20)
        .spawn(|| {
            let (expanded, c) = expanded_early_return_proof(128);
            assert!(brace_depth(&expanded) <= 4, "{}", brace_depth(&expanded));
            crate::surface::proof::without_implicit_solve(|| {
                verify_c_sources(&expanded, &[("mark.c", c.as_str())])
            })
            .unwrap_or_else(|error| panic!("128 returns reverify: {}", error.message()));
            let false_c = c.replace("    return 0;\n}", "    return -1;\n}");
            assert_ne!(false_c, c);
            crate::surface::proof::without_implicit_solve(|| {
                verify_c_sources(&expanded, &[("mark.c", false_c.as_str())])
            })
            .expect_err("the last path still owes its postcondition");
        })
        .unwrap()
        .join()
        .unwrap();
}

/// The proof `click expand` writes for [`early_return_project`]'s implicit
/// proof: each return in its own proof `if`, followed by the next case.
fn early_return_expanded_closers(returns: usize) -> String {
    let mut proof = format!(
        "verifying \"mark.c\";\nint32 mark(int32 *a, int32 x) {{\n    owns a[0..{returns}];\n    ensures result >= 0;\n}} by {{\n    step();\n"
    );
    for index in 0..returns {
        let statement = 1 + 4 * index;
        let last = if index + 1 == returns {
            "        close();\n        close();\n        close();\n        close();\n        close();\n"
        } else {
            ""
        };
        proof.push_str(&format!(
            "    if at(region({statement}).entry, x) == at(region({statement}).entry, {index}) {{\n        step();\n        step();\n        close();\n        close();\n        close();\n        close();\n        close();\n    }} else {{\n        step();\n        step();\n        step();\n{last}    }}\n"
        ));
    }
    proof.push_str("}\n");
    proof
}

/// Finishes and certifies the expanded proofs of [`early_return_project`]
/// and returns each operation the paths share prefixes in, net of the
/// listing of each path theorem's own premises, which is that theorem's
/// output: path `k` states its `k` case facts.
fn early_return_finishing_curves(sizes: &[usize]) -> Vec<(&'static str, Vec<usize>)> {
    let samples = std::thread::Builder::new()
        .name("early-return-finishing".into())
        .stack_size(64 << 20)
        .spawn({
            let sizes = sizes.to_vec();
            move || {
                sizes
                    .into_iter()
                    .map(|returns| {
                        let (_, c) = early_return_project(returns);
                        let expanded = early_return_expanded_closers(returns);
                        let materialized =
                            crate::kernel::assumptions::materialized_execution_facts();
                        let joined = crate::surface::proof::join_arm_effect_facts();
                        let indexed = crate::kernel::indexed_execution_facts();
                        let (verified, sample) = scaling_sample(returns, || {
                            crate::surface::proof::without_implicit_solve(|| {
                                verify_c_sources(&expanded, &[("mark.c", c.as_str())])
                            })
                        });
                        verified.unwrap_or_else(|error| {
                            panic!("{returns} returns reverify: {}", error.message())
                        });
                        (
                            sample,
                            crate::kernel::assumptions::materialized_execution_facts()
                                - materialized,
                            crate::surface::proof::join_arm_effect_facts() - joined,
                            crate::kernel::indexed_execution_facts() - indexed,
                        )
                    })
                    .collect::<Vec<_>>()
            }
        })
        .unwrap()
        .join()
        .unwrap();
    let counters = samples
        .iter()
        .map(|(_, materialized, joined, indexed)| (*materialized, *joined, *indexed))
        .collect::<Vec<_>>();
    let samples = samples
        .into_iter()
        .map(|(sample, _, _, _)| sample)
        .collect::<Vec<_>>();
    let named = |sample: &ScalingSample, name: &str| {
        sample
            .named_work
            .get(&format!("operation `{name}`"))
            .copied()
            .unwrap_or(0)
    };
    let premises = |sample: &ScalingSample| named(sample, "path theorem premises");
    let curve =
        |work: &dyn Fn(&ScalingSample) -> usize| samples.iter().map(work).collect::<Vec<_>>();
    vec![
        (
            "proof completion",
            curve(&|sample| named(sample, "proof completion") - premises(sample)),
        ),
        (
            "proof context finishing",
            curve(&|sample| named(sample, "proof context finishing") - premises(sample)),
        ),
        (
            "contract path preparation",
            curve(&|sample| named(sample, "contract path preparation")),
        ),
        (
            "contract claim: proposition",
            curve(&|sample| named(sample, "contract claim: proposition")),
        ),
        ("path theorem premises", curve(&premises)),
        (
            "completion fact delta",
            curve(&|sample| named(sample, "completion fact delta")),
        ),
        // Uncharged work: an outcome goal merging its path's fact and effect
        // streams, and a join taking its arms' effect suffixes. Each is the
        // path's or arm's whole history when it is not shared.
        (
            "materialized outcome facts",
            counters
                .iter()
                .map(|(materialized, _, _)| *materialized)
                .collect(),
        ),
        (
            "join arm effects",
            counters.iter().map(|(_, joined, _)| *joined).collect(),
        ),
        // Fact streams indexed from scratch when first queried: a path's
        // case facts stay indexed as they grow, and its published streams
        // are not indexed per path.
        (
            "indexed execution facts",
            counters.iter().map(|(_, _, indexed)| *indexed).collect(),
        ),
    ]
}

fn assert_early_return_finishing_shares_prefixes(sizes: &[usize]) {
    let curves = early_return_finishing_curves(sizes);
    eprintln!("early-return finishing curves at {sizes:?}: {curves:?}");
    for (name, work) in &curves {
        if *name == "path theorem premises" {
            continue;
        }
        // Completion indexes each path's facts once to list them as its
        // theorem's premises; any other index build must stay linear.
        if *name == "indexed execution facts" {
            let premises = &curves
                .iter()
                .find(|(name, _)| *name == "path theorem premises")
                .expect("premises curve")
                .1;
            for ((indexed, premises), size) in work.iter().zip(premises).zip(sizes) {
                assert!(
                    *indexed <= premises + 4 * size,
                    "facts indexed from scratch exceed the premises listed: {work:?}; all curves: {curves:?}"
                );
            }
            continue;
        }
        // A counter of uncharged work may stay at zero.
        let counter = matches!(
            *name,
            "materialized outcome facts" | "join arm effects" | "contract path preparation"
        );
        if *name == "contract path preparation" {
            assert!(
                work.iter().all(|units| *units == 0),
                "closed propositions must not rebuild contract paths: {work:?}"
            );
        }
        assert!(
            counter || *name == "completion fact delta" || work.iter().all(|units| *units > 0),
            "{name} was not measured: {work:?}"
        );
        assert!(
            work.windows(2)
                .all(|pair| pair[1] * 100 <= pair[0] * 225 + 100),
            "{name} grew faster than the paths it finishes: {work:?}; all curves: {curves:?}"
        );
    }
}

/// Finishing and certifying `N` sequential early returns costs each path its
/// own suffix. Completion, contract path preparation and outcome goals each
/// rebuilt every path's context from its whole prefix, which made the
/// expanded proof quadratic in `N` (at 8, 16, 32 and 64 returns, completion
/// cost 663, 2,139, 7,587 and 28,467 units and path preparation 1,843,
/// 4,127, 10,423 and 29,927).
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn early_return_finishing_shares_path_prefixes() {
    assert_early_return_finishing_shares_prefixes(&[4, 8, 16]);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: expands and re-verifies up to 64 early returns in a debug build"]
fn early_return_finishing_shares_path_prefixes_through_64_returns() {
    assert_early_return_finishing_shares_prefixes(&[8, 16, 32, 64]);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: four post-return unfold sizes take 0.94s in the parallel gate"]
fn post_return_function_equations_scale_with_explicit_unfolds() {
    let fixture = crate::cli::parse_mdtest(
        std::path::Path::new("return_fold_retains_post_return_function_unfold.md"),
        include_str!("../../../../mdtests/return_fold_retains_post_return_function_unfold.md"),
    )
    .unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    let samples = [4, 8, 16, 32].map(|size| {
        let unfolds = (0..size)
            .map(|index| format!("unfold(first(Shape::Pair(x, {index})));"))
            .collect::<Vec<_>>()
            .join("\n");
        let source = source.replace("unfold(first(Shape::Pair(x, 3)));", &unfolds);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            verify_c_sources(&source, &sources)
        });
        result.unwrap();
        work
    });
    assert!(samples[0] > 0);
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 2 * pair[0] + 64),
        "retained unfold equations rescanned the growing return proof: {samples:?}"
    );
}

/// A pointer a call returned is spelled `<region>.result` from one index
/// lookup, however many calls the path recorded; replacing or removing the
/// call's exit removes the spelling.
#[test]
fn recorded_pointer_call_results_scale_and_follow_replacement() {
    use crate::kernel::{Address, ProgramType, Variable};
    for size in [16usize, 64, 256, 1024] {
        let mut retained_states = RecordedStates::new();
        let value = |index: u64| {
            ProgramValue::typed_pointer(
                Address::symbolic(Variable(710_000 + index)),
                ProgramType::Int32Pointer,
            )
        };
        for index in 0..size {
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                retained_states.record_call_result(index, Some(value(index as u64)));
            });
            assert!(work <= 2, "{size}: insertion {work}");
        }
        let first = Address::symbolic(Variable(710_000));
        let (region, work) = crate::instrumentation::measure_deterministic_work(|| {
            retained_states.call_result_naming_pointer(&first)
        });
        assert_eq!(region, Some(CodeRegionRef::Region(0)));
        assert!(work <= 2, "{size}: lookup {work}");
        // A later call returning the same pointer does not take the name.
        retained_states.record_call_result(size, Some(value(0)));
        assert_eq!(
            retained_states.call_result_naming_pointer(&first),
            Some(CodeRegionRef::Region(0))
        );
        let branch = retained_states.clone();
        retained_states.record_call_result(0, Some(value(20_000)));
        assert!(retained_states.call_result_naming_pointer(&first).is_none());
        assert_eq!(
            branch.call_result_naming_pointer(&first),
            Some(CodeRegionRef::Region(0))
        );
        retained_states.record_call_result(0, None);
        assert!(retained_states.call_result_naming_pointer(&first).is_none());
    }
}

#[test]
fn recorded_call_results_scale_and_replace_execution_occurrences() {
    use crate::kernel::{MachineIntegerType, OldConditionTerm, OldMachineTerm, Variable};
    for size in [16usize, 64, 256, 1024] {
        let mut retained_states = RecordedStates::new();
        let value = |index| {
            ProgramValue::Bool(OldMachineTerm::bool_cast(
                MachineIntegerType::UInt8,
                OldConditionTerm::Variable(Variable(700_000 + index)),
            ))
        };
        for index in 0..size {
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                retained_states.record_call_result(index, Some(value(index as u64)));
            });
            assert!(work <= 2, "{size}: insertion {work}");
        }
        let ProgramValue::Bool(first) = value(0) else {
            unreachable!()
        };
        let (region, work) = crate::instrumentation::measure_deterministic_work(|| {
            retained_states.call_result_naming_integer(&first)
        });
        assert_eq!(region, Some(CodeRegionRef::Region(0)));
        assert!(work <= 2, "{size}: lookup {work}");
        let branch = retained_states.clone();
        retained_states.record_call_result(0, Some(value(10000)));
        assert!(retained_states.call_result_naming_integer(&first).is_none());
        assert_eq!(
            branch
                .region_result_value(&CodeRegionRef::Region(0))
                .unwrap(),
            value(0)
        );
        assert_eq!(
            retained_states
                .region_result_value(&CodeRegionRef::Region(0))
                .unwrap(),
            value(10000)
        );
        retained_states.record_call_result(0, None);
        assert!(
            retained_states
                .region_result_value(&CodeRegionRef::Region(0))
                .is_err()
        );
    }
}

#[test]
fn recorded_algebraic_field_names_use_changed_instances_and_direct_lookups() {
    use crate::kernel::model_fields::{ModelFieldOrigin, ModelMint, register_model_field_variable};
    use crate::kernel::{
        AlgebraicTerm, AlgebraicTermNode, AlgebraicType, AlgebraicValue, Variable,
    };
    let ty = AlgebraicType::parameter("T".into());
    let schema = crate::kernel::ResourceFieldSchema::new(vec![(
        "items".into(),
        crate::kernel::ResourceFieldType::Algebraic(ty.clone()),
    )])
    .unwrap();
    for size in [16usize, 64, 256, 1024] {
        let mut retained_states = RecordedStates::new();
        let mut state = ExecutionState::new();
        for index in 0..size {
            let variable = Variable(900_000 + index as u64);
            let identity =
                crate::kernel::InstanceId::from_variable(Variable(800_000 + index as u64));
            register_model_field_variable(
                variable,
                ModelFieldOrigin {
                    identity,
                    field: "items".into(),
                    field_index: 0,
                    minted_by: ModelMint::CallReturn {
                        callee: "update".into(),
                    },
                },
            );
            let instance = crate::kernel::ResourceInstance::new(
                identity,
                "object".into(),
                vec![].into(),
                schema.clone(),
                vec![AlgebraicValue::Algebraic(AlgebraicTerm {
                    algebraic_type: ty.clone(),
                    node: AlgebraicTermNode::Variable(variable),
                })]
                .into(),
            )
            .unwrap();
            let resources =
                state
                    .resources()
                    .clone()
                    .unchecked_with_fact(crate::kernel::ResourceFact::own(
                        crate::kernel::Resource::Instance(instance),
                    ));
            state = state.with_resource_context(resources);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                retained_states.insert(
                    ProgramPointRef {
                        region: CodeRegionRef::Region(index),
                        kind: ProgramPointKind::Exit,
                    },
                    state.clone(),
                );
            });
            assert!(work <= 4, "{size}/{index}: insertion {work}");
        }
        let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
            retained_states
                .point_holding_field_value(Variable(900_000))
                .is_some()
        });
        assert!(found);
        assert!(work <= 4, "{size}: lookup {work}");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: end-to-end explicit claim closing scaling; 2.8s under build load"]
fn explicit_claim_closers_have_near_linear_finishing_work() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = grouped_claim_project(size);
            let click_source = click_source.replace("    close();", &"    close();\n".repeat(size));
            let (verified, sample) = scaling_sample(size, || {
                verify_c_sources(&click_source, &[("shared_claims.c", c_source.as_str())])
            });
            assert_eq!(verified.unwrap().len(), size);
            sample
        })
        .collect::<Vec<_>>();
    let work = samples
        .iter()
        .map(|sample| sample.named_work["operation `proof context finishing`"])
        .collect::<Vec<_>>();
    assert!(work.iter().all(|units| *units > 0));
    for pair in work.windows(2) {
        assert!(pair[1] <= 3 * pair[0], "explicit closer work: {work:?}");
    }
}

/// Write the adjacent read equalities used by the replay scaling fixtures.
fn written_preservation_links(stores: usize, read: &str) -> String {
    (0..stores)
        .map(|i| format!(
            "have at(statement({i}).exit, {read}) == at(statement({i}).entry, {read}) by {{ preserve(memory({read}), statement({i})); }}\n"
        ))
        .collect()
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.0s in the parallel gate"]
fn multi_statement_transport_replay_scales_with_explicit_links() {
    let mut costs = Vec::new();
    for size in [2, 4, 8, 16] {
        let c = format!(
            "void keep(unsigned char *p, unsigned char *q) {{ {} }}",
            (0..size).map(|i| format!("*p = {i};")).collect::<String>()
        );
        let separations = (0..size)
            .map(|i| {
                format!(
                    "step(); have separate(statement({i}).footprint, memory(*q)) by {{ close(); }}"
                )
            })
            .collect::<String>();
        let links = written_preservation_links(size, "*q");
        let source = format!(
            r#"
            verifying "chain.c";
            void keep(uint8* p, uint8* q) {{
                owns *p; views *q; requires separate(memory(*p), memory(*q));
            }} by {{
                {separations}
                have *q == at(statement(0).entry, *q) by {{
                    {links} close();
                }}
                step();
            }}
        "#
        );
        let sources = [("chain.c", c.as_str())];
        let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
        assert_eq!(expanded.matches("preserve(").count(), size);
        assert!(!expanded.contains("transport("));
        assert!(!expanded.contains("transport_certificate"));
        let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::surface::proof::without_implicit_solve(|| verify_c_sources(&expanded, &sources))
        });
        verified.unwrap();
        costs.push(work);
    }
    eprintln!("multi-statement replay work: {costs:?}");
    assert!(costs.iter().all(|cost| *cost > 0));
    assert!(
        costs.windows(2).all(|pair| pair[1] <= pair[0] * 3),
        "{costs:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.0s in the parallel gate"]
fn inequality_transport_replay_scales_with_explicit_links() {
    let mut costs = Vec::new();
    for size in [2, 4, 8, 16] {
        let c = format!(
            "void keep(int *p, int *q) {{ {} }}",
            (0..size).map(|i| format!("*p = {i};")).collect::<String>()
        );
        let separations = (0..size)
            .map(|i| {
                format!(
                    "step(); have separate(statement({i}).footprint, memory(*q)) by {{ close(); }}"
                )
            })
            .collect::<String>();
        let links = written_preservation_links(size, "*q");
        let source = format!(
            r#"
            verifying "chain.c";
            void keep(int32* p, int32* q) {{
                owns *p; views *q; requires separate(memory(*p), memory(*q)); requires *q > 0;
            }} by {{
                {separations}
                have *q > 0 by {{
                    {links} close();
                }}
                step();
            }}
        "#
        );
        let sources = [("chain.c", c.as_str())];
        let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
        assert_eq!(expanded.matches("preserve(").count(), size);
        assert!(!expanded.contains("transport("));
        assert!(!expanded.contains("transport_certificate"));
        let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::surface::proof::without_implicit_solve(|| verify_c_sources(&expanded, &sources))
        });
        verified.unwrap();
        costs.push(work);
    }
    eprintln!("inequality replay work: {costs:?}");
    assert!(costs.iter().all(|cost| *cost > 0));
    assert!(
        costs.windows(2).all(|pair| pair[1] <= pair[0] * 3),
        "{costs:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.0s in the parallel gate"]
fn known_value_transport_replay_scales_with_explicit_links() {
    let mut costs = Vec::new();
    for size in [2, 4, 8, 16] {
        let c = format!(
            "void keep(int *p, int *q) {{ {} }}",
            (0..size).map(|i| format!("*p = {i};")).collect::<String>()
        );
        let separations = (0..size)
            .map(|i| {
                format!(
                    "step(); have separate(statement({i}).footprint, memory(*q)) by {{ close(); }}"
                )
            })
            .collect::<String>();
        let links = written_preservation_links(size, "*q");
        let source = format!(
            r#"
            verifying "chain.c";
            void keep(int32* p, int32* q) {{
                owns *p; views *q; requires separate(memory(*p), memory(*q)); requires *q == 7;
            }} by {{
                {separations}
                have *q == 7 by {{
                    {links} close();
                }}
                step();
            }}
        "#
        );
        let sources = [("chain.c", c.as_str())];
        let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
        assert_eq!(expanded.matches("preserve(").count(), size);
        assert!(!expanded.contains("transport("));
        assert!(!expanded.contains("transport_certificate"));
        let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::surface::proof::without_implicit_solve(|| verify_c_sources(&expanded, &sources))
        });
        verified.unwrap();
        costs.push(work);
    }
    eprintln!("known-value replay work: {costs:?}");
    assert!(costs.iter().all(|cost| *cost > 0));
    assert!(
        costs.windows(2).all(|pair| pair[1] <= pair[0] * 3),
        "{costs:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.0s in the parallel gate"]
fn state_comparison_transport_replay_scales_with_explicit_links() {
    let mut costs = Vec::new();
    for size in [2, 4, 8, 16] {
        let c = format!(
            "void keep(int *p, int *q) {{ {} }}",
            (0..size).map(|i| format!("*p = {i};")).collect::<String>()
        );
        let separations = (0..size)
            .map(|i| {
                format!(
                    "step(); have separate(statement({i}).footprint, memory(*q)) by {{ close(); }}"
                )
            })
            .collect::<String>();
        let links = written_preservation_links(size, "*q");
        let source = format!(
            r#"
            verifying "chain.c";
            void keep(int32* p, int32* q) {{
                owns *p; views *q; requires separate(memory(*p), memory(*q)); requires *q == 7;
            }} by {{
                {separations}
                have *q == 7 by {{
                    {links} close();
                }}
                step();
            }}
        "#
        );
        let sources = [("chain.c", c.as_str())];
        let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
        assert_eq!(expanded.matches("preserve(").count(), size);
        assert!(!expanded.contains("transport("));
        assert!(!expanded.contains("transport_certificate"));
        let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::surface::proof::without_implicit_solve(|| verify_c_sources(&expanded, &sources))
        });
        verified.unwrap();
        costs.push(work);
    }
    eprintln!("state-comparison replay work: {costs:?}");
    assert!(costs.iter().all(|cost| *cost > 0));
    assert!(
        costs.windows(2).all(|pair| pair[1] <= pair[0] * 3),
        "{costs:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3.3s in the parallel gate"]
fn two_read_transport_replay_scales_with_explicit_links() {
    two_read_transport_replay_cost(false);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: indexed transport expansion and cold replay at four chain lengths"]
fn indexed_read_transport_replay_scales_with_explicit_links() {
    two_read_transport_replay_cost(true);
}

fn two_read_transport_replay_cost(indexed: bool) {
    let mut costs = Vec::new();
    for size in [2, 4, 8, 16] {
        let c = format!(
            "void keep(int *p, int *q, int *r) {{ {} }}",
            (0..size).map(|i| format!("*p = {i};")).collect::<String>()
        );
        let mut setup = String::new();
        let links =
            written_preservation_links(size, "*q") + &written_preservation_links(size, "*r");
        for i in 0..size {
            setup.push_str("step();");
            for read in ["q", "r"] {
                setup.push_str(&format!(
                    "have separate(statement({i}).footprint, memory(*{read})) by {{ close(); }}"
                ));
            }
        }
        let source = format!(
            r#"
            verifying "chain.c";
            void keep(int32* p, int32* q, int32* r) {{
                owns *p; views *q; views *r;
                requires separate(memory(*p), memory(*q));
                requires separate(memory(*p), memory(*r));
                requires *q == *r;
            }} by {{
                {setup}
                have *q == *r by {{
                    {links} close();
                }}
                step();
            }}
        "#
        );
        let source = if indexed {
            source.replace("*q", "q[0]").replace("*r", "q[1]")
        } else {
            source
        };
        let sources = [("chain.c", c.as_str())];
        let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
        assert_eq!(expanded.matches("preserve(").count(), 2 * size);
        assert!(!expanded.contains("transport("));
        assert!(!expanded.contains("transport_certificate"));
        let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::surface::proof::without_implicit_solve(|| verify_c_sources(&expanded, &sources))
        });
        verified.unwrap();
        costs.push(work);
    }
    eprintln!("two-read replay work: {costs:?}");
    assert!(costs.iter().all(|cost| *cost > 0));
    assert!(
        costs.windows(2).all(|pair| pair[1] <= pair[0] * 3),
        "{costs:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3.4s in the parallel gate"]
fn conjunction_transport_replay_scales_with_explicit_links() {
    let mut costs = Vec::new();
    for size in [2, 4, 8, 16] {
        let c = format!(
            "void keep(int *p, int *q, int *r) {{ {} }}",
            (0..size).map(|i| format!("*p = {i};")).collect::<String>()
        );
        let mut setup = String::new();
        let links =
            written_preservation_links(size, "*q") + &written_preservation_links(size, "*r");
        for i in 0..size {
            setup.push_str("step();");
            for read in ["q", "r"] {
                setup.push_str(&format!(
                    "have separate(statement({i}).footprint, memory(*{read})) by {{ close(); }}"
                ));
            }
        }
        let source = format!(
            r#"
            verifying "chain.c";
            void keep(int32* p, int32* q, int32* r) {{
                owns *p; views *q; views *r;
                requires separate(memory(*p), memory(*q));
                requires separate(memory(*p), memory(*r));
                requires *q == 7 and *r == 8;
            }} by {{
                {setup}
                have *q == 7 and *r == 8 by {{
                    {links} close();
                }}
                step();
            }}
        "#
        );
        let sources = [("chain.c", c.as_str())];
        let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
        assert_eq!(expanded.matches("preserve(").count(), 2 * size);
        assert!(!expanded.contains("transport("));
        assert!(!expanded.contains("transport_certificate"));
        let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::surface::proof::without_implicit_solve(|| verify_c_sources(&expanded, &sources))
        });
        verified.unwrap();
        costs.push(work);
    }
    eprintln!("conjunction replay work: {costs:?}");
    assert!(costs.iter().all(|cost| *cost > 0));
    assert!(
        costs.windows(2).all(|pair| pair[1] <= pair[0] * 3),
        "{costs:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: full skewed conjunction expansion and cold replay scaling audit"]
fn nested_conjunction_transport_scales_with_written_leaves() {
    nested_conjunction_transport_scaling(false);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 13s focused, balanced conjunction expansion and cold replay scaling audit"]
fn balanced_nested_conjunction_transport_scales_with_written_leaves() {
    nested_conjunction_transport_scaling(true);
}

fn nested_conjunction_transport_scaling(balanced: bool) {
    fn conjunction(leaves: &[String], balanced: bool) -> String {
        if leaves.len() == 1 {
            return leaves[0].clone();
        }
        let split = if balanced { leaves.len() / 2 } else { 1 };
        format!(
            "({}) and ({})",
            conjunction(&leaves[..split], balanced),
            conjunction(&leaves[split..], balanced)
        )
    }
    let mut planning = Vec::new();
    let mut replay = Vec::new();
    // Skewed syntax must stay within the existing parenthesis/proof depth
    // limits. Balanced trees exercise larger leaf and premise counts.
    let sizes = if balanced {
        [4, 8, 16, 32]
    } else {
        [2, 4, 8, 12]
    };
    for size in sizes {
        let mut c_args = String::new();
        let mut args = String::new();
        let mut requirements = String::new();
        let mut setup = String::new();
        let mut links = String::new();
        for i in 0..size {
            c_args.push_str(&format!(", int *q{i}"));
            args.push_str(&format!(", int32* q{i}"));
            requirements.push_str(&format!(
                "views *q{i}; requires separate(memory(*p), memory(*q{i}));"
            ));
            setup.push_str(&format!("have separate(statement(0).footprint, memory(*q{i})) by {{ close() using {{ separate(memory(*p), memory(*q{i})); }}; }}"));
            links.push_str(&written_preservation_links(1, &format!("*q{i}")));
        }
        let leaves = (0..size)
            .map(|i| format!("*q{i} == {i}"))
            .collect::<Vec<_>>();
        let fact = conjunction(&leaves, balanced);
        let c = format!("void keep(int *p{c_args}) {{ *p = 0; }}");
        let source = format!(
            r#"
                verifying "nested.c";
                void keep(int32* p{args}) {{ owns *p; {requirements} requires {fact}; }} by {{
                    step(); {setup}
                    have {fact} by {{ {links} close(); }}
                    step();
                }}
            "#
        );
        let files = [("nested.c", c.as_str())];
        let (expanded, work) = crate::instrumentation::measure_deterministic_work(|| {
            expand_c_claim_source_by_label(&source, &files, "keep.contract")
        });
        let expanded = expanded.unwrap();
        planning.push(work);
        assert_eq!(expanded.matches("have *q0 == 0 and").count(), 1);
        assert_eq!(expanded.matches("preserve(").count(), size);
        assert!(!expanded.contains("transport("));
        assert!(!expanded.contains("transport_certificate"));
        let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::surface::proof::without_implicit_solve(|| verify_c_sources(&expanded, &files))
        });
        verified.unwrap();
        replay.push(work);
    }
    eprintln!("nested conjunction balanced={balanced}: expansion {planning:?}, replay {replay:?}");
    for costs in [planning, replay] {
        assert!(costs.iter().all(|cost| *cost > 0));
        assert!(
            costs.windows(2).all(|pair| pair[1] <= 3 * pair[0]),
            "{costs:?}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: full conjunction projection expansion and cold replay scaling audit"]
fn conjunction_projection_transport_scales_with_written_source() {
    fn balanced(leaves: &[String]) -> String {
        if leaves.len() == 1 {
            return leaves[0].clone();
        }
        let middle = leaves.len() / 2;
        format!(
            "({}) and ({})",
            balanced(&leaves[..middle]),
            balanced(&leaves[middle..])
        )
    }
    let mut expansion = Vec::new();
    let mut replay = Vec::new();
    for size in [4, 8, 16, 32] {
        let mut leaves = (0..size - 1)
            .map(|i| format!("*p >= {i}"))
            .collect::<Vec<_>>();
        leaves.push("*q == 7".to_owned());
        let fact = balanced(&leaves);
        let links = written_preservation_links(1, "*q");
        let source = format!(
            r#"
            verifying "projection.c";
            void keep(int32* p, int32* q) {{
                owns *p; views *q;
                requires separate(memory(*p), memory(*q));
                requires {fact};
            }} by {{
                step();
                have separate(statement(0).footprint, memory(*q)) by {{
                    close();
                }}
                have *q == 7 by {{
                    {links} close();
                }}
                step();
            }}
        "#
        );
        let files = [("projection.c", "void keep(int *p, int *q) { *p = 0; }")];
        let (expanded, work) = crate::instrumentation::measure_deterministic_work(|| {
            expand_c_claim_source_by_label(&source, &files, "keep.contract")
        });
        let expanded = expanded.unwrap();
        expansion.push(work);
        assert_eq!(expanded.matches("preserve(").count(), 1);
        assert!(!expanded.contains("all {"));
        assert!(!expanded.contains("transport("));
        assert!(!expanded.contains("transport_certificate"));
        let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::surface::proof::without_implicit_solve(|| verify_c_sources(&expanded, &files))
        });
        verified.unwrap();
        replay.push(work);
    }
    eprintln!("conjunction projection: expansion {expansion:?}, replay {replay:?}");
    for costs in [expansion, replay] {
        assert!(costs.iter().all(|cost| *cost > 0));
        assert!(costs.windows(2).all(|p| p[1] <= 3 * p[0]), "{costs:?}");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 10s focused, full expansion and replay scaling audit"]
fn conjunction_selection_transport_scales_with_sources_targets_and_premises() {
    fn balanced(leaves: &[String]) -> String {
        if leaves.len() == 1 {
            return leaves[0].clone();
        }
        let middle = leaves.len() / 2;
        format!(
            "({}) and ({})",
            balanced(&leaves[..middle]),
            balanced(&leaves[middle..])
        )
    }
    let mut expansion = Vec::new();
    let mut replay = Vec::new();
    for size in [4, 8, 16, 32] {
        let mut c_args = String::new();
        let mut args = String::new();
        let mut requirements = String::new();
        let mut setup = String::new();
        let mut links = String::new();
        for i in 0..size {
            c_args.push_str(&format!(", int *q{i}"));
            args.push_str(&format!(", int32* q{i}"));
            requirements.push_str(&format!(
                "views *q{i}; requires separate(memory(*p), memory(*q{i}));"
            ));
            if i % 2 == 0 {
                setup.push_str(&format!(
                    "have separate(statement(0).footprint, memory(*q{i})) by {{ close(); }}"
                ));
                links.push_str(&written_preservation_links(1, &format!("*q{i}")));
            }
        }
        let mut leaves = (0..size)
            .map(|i| format!("*q{i} == {i}"))
            .collect::<Vec<_>>();
        let chosen = leaves.iter().step_by(2).rev().cloned().collect::<Vec<_>>();
        leaves.push("*p == 99".to_owned());
        let source_fact = balanced(&leaves);
        let target = balanced(&chosen);
        let c = format!("void keep(int *p{c_args}) {{ *p = 0; }}");
        let source = format!(
            r#"
            verifying "selection.c";
            void keep(int32* p{args}) {{ owns *p; {requirements} requires {source_fact}; }} by {{
                step(); {setup}
                have {target} by {{ {links} close(); }}
                step();
            }}
        "#
        );
        let files = [("selection.c", c.as_str())];
        let (expanded, work) = crate::instrumentation::measure_deterministic_work(|| {
            expand_c_claim_source_by_label(&source, &files, "keep.contract")
        });
        let expanded = expanded.unwrap();
        expansion.push(work);
        assert_eq!(expanded.matches("preserve(").count(), size / 2);
        assert!(!expanded.contains("transport("));
        assert!(!expanded.contains("transport_certificate"));
        let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::surface::proof::without_implicit_solve(|| verify_c_sources(&expanded, &files))
        });
        verified.unwrap();
        replay.push(work);
    }
    eprintln!("conjunction selection: expansion {expansion:?}, replay {replay:?}");
    for costs in [expansion, replay] {
        assert!(costs.iter().all(|cost| *cost > 0));
        assert!(costs.windows(2).all(|p| p[1] <= 3 * p[0]), "{costs:?}");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3.1s in the parallel gate"]
fn implication_transport_replay_scales_with_explicit_links() {
    let mut costs = Vec::new();
    for size in [2, 4, 8, 16] {
        let c = format!(
            "void keep(int *p, int *q, int *r) {{ {} }}",
            (0..size).map(|i| format!("*p = {i};")).collect::<String>()
        );
        let mut setup = String::new();
        let links =
            written_preservation_links(size, "*q") + &written_preservation_links(size, "*r");
        for i in 0..size {
            setup.push_str("step();");
            for read in ["q", "r"] {
                setup.push_str(&format!(
                    "have separate(statement({i}).footprint, memory(*{read})) by {{ close(); }}"
                ));
            }
        }
        let source = format!(
            r#"
            verifying "chain.c";
            void keep(int32* p, int32* q, int32* r) {{
                owns *p; views *q; views *r;
                requires separate(memory(*p), memory(*q));
                requires separate(memory(*p), memory(*r));
                requires *q == 7 implies *r == 8;
            }} by {{
                {setup}
                have *q == 7 implies *r == 8 by {{
                    {links} close();
                }}
                step();
            }}
        "#
        );
        let sources = [("chain.c", c.as_str())];
        let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
        assert_eq!(expanded.matches("preserve(").count(), 2 * size);
        assert!(!expanded.contains("transport("));
        assert!(!expanded.contains("transport_certificate"));
        let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::surface::proof::without_implicit_solve(|| verify_c_sources(&expanded, &sources))
        });
        verified.unwrap();
        costs.push(work);
    }
    eprintln!("implication replay work: {costs:?}");
    assert!(costs.iter().all(|cost| *cost > 0));
    assert!(
        costs.windows(2).all(|pair| pair[1] <= pair[0] * 3),
        "{costs:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 15s focused, full expansion and replay scaling audit"]
fn compound_implication_transport_scales_with_reads_and_logical_depth() {
    fn tree(leaves: &[String], op: &str, skewed: bool) -> String {
        if leaves.len() == 1 {
            return leaves[0].clone();
        }
        let middle = if skewed { 1 } else { leaves.len() / 2 };
        format!(
            "({}) {op} ({})",
            tree(&leaves[..middle], op, skewed),
            tree(&leaves[middle..], op, skewed)
        )
    }
    // Distinct reads with a wide guard; distinct reads under nested implications;
    // repeated uses of two reads in a wide guard. Stay within parser depth limits.
    for mode in [0, 1, 2] {
        let mut expansion = Vec::new();
        let mut replay = Vec::new();
        let sizes = if mode == 1 {
            [2, 4, 8, 12]
        } else {
            [4, 8, 16, 32]
        };
        for size in sizes {
            let read_count = if mode == 2 { 2 } else { size };
            let mut c_args = String::new();
            let mut args = String::new();
            let mut requirements = String::new();
            let mut setup = String::new();
            let mut links = String::new();
            for i in 0..read_count {
                c_args.push_str(&format!(", int *q{i}"));
                args.push_str(&format!(", int32* q{i}"));
                requirements.push_str(&format!(
                    "views *q{i}; requires separate(memory(*p), memory(*q{i}));"
                ));
                setup.push_str(&format!(
                    "have separate(statement(0).footprint, memory(*q{i})) by {{ close(); }}"
                ));
                links.push_str(&written_preservation_links(1, &format!("*q{i}")));
            }
            let leaves = (0..size)
                .map(|i| {
                    if mode == 2 {
                        if i == size - 1 {
                            "*q1 == 8".to_owned()
                        } else {
                            format!("*q0 >= {i}")
                        }
                    } else {
                        format!("*q{i} == {i}")
                    }
                })
                .collect::<Vec<_>>();
            let fact = if mode == 1 {
                tree(&leaves, "implies", true)
            } else {
                format!(
                    "({}) implies {}",
                    tree(&leaves[..size - 1], "and", false),
                    leaves[size - 1]
                )
            };
            let c = format!("void keep(int *p{c_args}) {{ *p = 0; }}");
            let source = format!(
                r#"
                verifying "compound.c";
                void keep(int32* p{args}) {{ owns *p; {requirements} requires {fact}; }} by {{
                    step(); {setup}
                    have {fact} by {{ {links} close(); }}
                    step();
                }}
            "#
            );
            let files = [("compound.c", c.as_str())];
            let (expanded, work) = crate::instrumentation::measure_deterministic_work(|| {
                expand_c_claim_source_by_label(&source, &files, "keep.contract")
            });
            let expanded = expanded.unwrap();
            expansion.push(work);
            assert_eq!(expanded.matches("preserve(").count(), read_count);
            assert!(!expanded.contains("rewrite("));
            assert!(!expanded.contains("transport("));
            assert!(!expanded.contains("transport_certificate"));
            let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::surface::proof::without_implicit_solve(|| {
                    verify_c_sources(&expanded, &files)
                })
            });
            verified.unwrap();
            replay.push(work);
        }
        eprintln!("compound implication mode={mode}: expansion {expansion:?}, replay {replay:?}");
        for costs in [expansion, replay] {
            assert!(costs.iter().all(|cost| *cost > 0));
            assert!(costs.windows(2).all(|p| p[1] <= 3 * p[0]), "{costs:?}");
        }
    }
}

#[test]
fn volatile_read_results_use_selected_event_indexes() {
    use crate::kernel::{OldMachineTerm, Variable};
    let mut samples = Vec::new();
    let mut repeated_samples = Vec::new();
    for size in [16usize, 64, 256, 1024] {
        let mut points = RecordedStates::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                let value =
                    ProgramValue::Int32(OldMachineTerm::Variable(Variable(800000 + index as u64)));
                points.record_read_event_values(index, std::iter::once(&value));
                assert!(points.read_event_naming_value(&value).is_some());
            }
        });
        samples.push(work);
        let first = ProgramValue::Int32(OldMachineTerm::Variable(Variable(800000)));
        let branch = points.clone();
        points.record_read_event_values(0, std::iter::empty());
        assert!(points.read_event_naming_value(&first).is_none());
        assert!(branch.read_event_naming_value(&first).is_some());
        assert!(
            points
                .region_result_value(&CodeRegionRef::Region(0))
                .is_err()
        );
        assert_eq!(
            branch
                .region_result_value(&CodeRegionRef::Region(0))
                .unwrap(),
            first
        );
        let (_, repeated_work) = crate::instrumentation::measure_deterministic_work(|| {
            points.record_read_event_values(size, std::iter::repeat_n(&first, size));
            points.record_read_event_values(size + 1, std::iter::once(&first));
            points.record_read_event_values(size + 1, std::iter::empty());
            assert_eq!(
                points.read_event_naming_value(&first),
                Some(points.read_event_region(size, size - 1))
            );
            points.record_read_event_values(size, std::iter::empty());
            assert!(points.read_event_naming_value(&first).is_none());
        });
        repeated_samples.push(repeated_work);
        points.insert(
            ProgramPointRef {
                region: CodeRegionRef::Region(0),
                kind: ProgramPointKind::Exit,
            },
            crate::kernel::ExecutionState::new(),
        );
        points.record_read_event_values(0, std::iter::once(&first));
        points.remove(&ProgramPointRef {
            region: CodeRegionRef::Region(0),
            kind: ProgramPointKind::Exit,
        });
        assert!(points.read_event_naming_value(&first).is_none());
    }
    for samples in [samples, repeated_samples] {
        assert!(
            samples.windows(2).all(|pair| pair[1] <= pair[0] * 6 + 128),
            "{samples:?}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.5s in the parallel gate"]
fn entry_separation_of_an_unconditional_resource_scales_with_the_owned_clauses() {
    // Run on the CLI's eight-megabyte stack, as `click verify` does.
    std::thread::Builder::new()
        .name("entry-separation-scaling".into())
        .stack_size(8 * 1024 * 1024)
        .spawn(entry_separation_samples)
        .unwrap()
        .join()
        .unwrap();
}

fn entry_separation_samples() {
    // The contract entry states the held resources as owned members beside
    // the members their unconditional bodies expand to. One selected
    // separation must not pay for the other owned clauses pairwise.
    let mut samples = Vec::new();
    for size in [4, 8, 16] {
        let parameters = (0..size)
            .map(|i| format!("struct node *p{i}, "))
            .collect::<String>();
        let c = format!(
            "struct node {{ struct node *next; }};\nvoid caller({parameters}int *slot) {{ }}\n"
        );
        let click_parameters = (0..size)
            .map(|i| format!("struct node* p{i}, "))
            .collect::<String>();
        let owned = (0..size)
            .map(|i| format!("    owns plain(p{i});\n"))
            .collect::<String>();
        let source = format!(
            "verifying \"owned.c\";\n\
             resource plain(p: struct node*) {{ owns p->next; }}\n\
             void caller({click_parameters}int32* slot) {{\n{owned}    owns *slot;\n}} by {{\n\
             have separate(plain(p0), memory(*slot)) by {{ close(); }}\n}}\n"
        );
        let sources = [("owned.c", c.as_str())];
        let (result, sample) = scaling_sample(size, || verify_c_sources(&source, &sources));
        result.expect("an owned unconditional resource is separate from another owned cell");
        samples.push(sample);
    }
    assert_near_linear_scaling_at_sampled_sizes(
        "entry separation of an unconditional resource",
        &samples,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn separation_of_an_owned_instance_scales_with_owned_clauses_and_steps() {
    // Run on the CLI's eight-megabyte stack, as `click verify` does.
    std::thread::Builder::new()
        .name("instance-separation-scaling".into())
        .stack_size(8 * 1024 * 1024)
        .spawn(instance_separation_samples)
        .unwrap()
        .join()
        .unwrap();
}

fn instance_separation_samples() {
    // One selected separation of a field-bearing instance from an owned
    // cell. `clauses` grows the other instances owned beside it; `steps`
    // grows the local statements executed while it is held, each of which
    // may state the held resources again.
    let fixture = |clauses: usize, steps: usize| {
        let parameters = (0..clauses)
            .map(|i| format!("struct node *p{i}, "))
            .collect::<String>();
        let locals = (0..steps)
            .map(|i| format!("int x{i} = 0; "))
            .collect::<String>();
        let c = format!(
            "struct node {{ struct node *next; }};\n\
             void caller({parameters}int *slot) {{ {locals}}}\n"
        );
        let click_parameters = (0..clauses)
            .map(|i| format!("struct node* p{i}, "))
            .collect::<String>();
        let owned = (0..clauses)
            .map(|i| format!("    owns b{i}: box(p{i});\n"))
            .collect::<String>();
        let stepped = "step(); ".repeat(steps);
        let source = format!(
            "verifying \"owned.c\";\n\
             resource box(p: struct node*) {{ field tag: int32; if p != 0 {{ owns p->next; }} }}\n\
             void caller({click_parameters}int32* slot) {{\n{owned}    owns *slot;\n}} by {{\n\
             {stepped}\n\
             have separate(b0, memory(*slot)) by {{ close(); }}\n}}\n"
        );
        (c, source)
    };
    for (label, sizes) in [
        ("owned clauses", [(4, 0), (8, 0), (16, 0)]),
        ("steps while held", [(2, 4), (2, 8), (2, 16)]),
    ] {
        let mut samples = Vec::new();
        for (clauses, steps) in sizes {
            let (c, source) = fixture(clauses, steps);
            let sources = [("owned.c", c.as_str())];
            let (result, sample) =
                scaling_sample(clauses.max(steps), || verify_c_sources(&source, &sources));
            result.expect("an owned instance is separate from another owned cell");
            samples.push(sample);
        }
        assert_near_linear_scaling_at_sampled_sizes(
            &format!("separation of an owned instance: {label}"),
            &samples,
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3.7s in the parallel gate"]
fn separation_of_a_folded_instance_scales_with_owned_clauses_and_folds() {
    // Run on the CLI's eight-megabyte stack, as `click verify` does.
    std::thread::Builder::new()
        .name("folded-instance-separation-scaling".into())
        .stack_size(8 * 1024 * 1024)
        .spawn(folded_instance_separation_samples)
        .unwrap()
        .join()
        .unwrap();
}

fn folded_instance_separation_samples() {
    // One selected separation of a just-folded instance from an owned cell,
    // read from the state's own resources. `clauses` grows the instances
    // owned beside it; `folds` grows how many of them the proof refolds
    // first, so the state holds that many other folded instances.
    let fixture = |clauses: usize, folds: usize| {
        let parameters = (0..clauses)
            .map(|i| format!("struct node *p{i}, "))
            .collect::<String>();
        let c = format!(
            "struct node {{ struct node *next; }};\n\
             void caller({parameters}int *slot) {{ }}\n"
        );
        let click_parameters = (0..clauses)
            .map(|i| format!("struct node* p{i}, "))
            .collect::<String>();
        let owned = (0..clauses)
            .map(|i| {
                if i < folds {
                    format!("    consumes b{i}: box(p{i});\n    produces d{i}: box(p{i});\n")
                } else {
                    format!("    owns b{i}: box(p{i});\n")
                }
            })
            .collect::<String>();
        let refolded = (0..folds)
            .map(|i| format!("unfold(b{i}); let d{i} = fold(box(p{i}), {{ tag: 0 }});\n"))
            .collect::<String>();
        let source = format!(
            "verifying \"owned.c\";\n\
             resource box(p: struct node*) {{ field tag: int32; owns p->next; }}\n\
             void caller({click_parameters}int32* slot) {{\n{owned}    owns *slot;\n}} by {{\n\
             {refolded}\
             have separate(d0, memory(*slot)) by {{ close(); }}\n}}\n"
        );
        (c, source)
    };
    for (label, sizes) in [
        ("owned clauses", [(4, 1), (8, 1), (16, 1)]),
        ("folded instances", [(16, 4), (16, 8), (16, 16)]),
    ] {
        let mut samples = Vec::new();
        for (clauses, folds) in sizes {
            let (c, source) = fixture(clauses, folds);
            let sources = [("owned.c", c.as_str())];
            let size = if label == "owned clauses" {
                clauses
            } else {
                folds
            };
            let (result, sample) = scaling_sample(size, || verify_c_sources(&source, &sources));
            result.expect("a folded instance is separate from another owned cell");
            samples.push(sample);
        }
        assert_near_linear_scaling_at_sampled_sizes(
            &format!("separation of a folded instance: {label}"),
            &samples,
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3.1s in the parallel gate"]
fn consuming_call_bound_scales_with_its_transferred_inputs() {
    // Run on the CLI's eight-megabyte stack, as `click verify` does.
    std::thread::Builder::new()
        .name("consuming-call-bound-scaling".into())
        .stack_size(8 * 1024 * 1024)
        .spawn(consuming_call_bound_samples)
        .unwrap()
        .join()
        .unwrap();
}

fn consuming_call_bound_samples() {
    // One call that consumes `size` field-bearing instances and produces as
    // many. The bound is one pass over the transferred inputs, so the call's
    // work grows linearly with them.
    let mut samples = Vec::new();
    for size in [4, 8, 16] {
        let parameters = (0..size)
            .map(|i| format!("struct node *p{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let arguments = (0..size)
            .map(|i| format!("p{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let c = format!(
            "struct node {{ struct node *next; }};\n\
             void touch({parameters}) {{}}\n\
             void caller({parameters}) {{ touch({arguments}); }}\n"
        );
        let click_parameters = (0..size)
            .map(|i| format!("struct node* p{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let clauses = (0..size)
            .map(|i| format!("    consumes b{i}: box(p{i});\n    produces c{i}: box(p{i});\n"))
            .collect::<String>();
        let refold = (0..size)
            .map(|i| format!("    unfold(b{i}); let c{i} = fold(box(p{i}), {{ tag: 0 }});\n"))
            .collect::<String>();
        let bindings = (0..size)
            .map(|i| format!("b{i}: b{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let outputs = (0..size)
            .map(|i| format!("c{i}: c{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let source = format!(
            "verifying \"consuming.c\";\n\
             resource box(p: struct node*) {{ field tag: int32; owns p->next; }}\n\
             void touch({click_parameters}) {{\n{clauses}}} by {{\n{refold}}}\n\
             void caller({click_parameters}) {{\n{clauses}}} by {{\n\
             let {{ {outputs} }} = step(touch, {{ {bindings} }});\n}}\n"
        );
        let sources = [("consuming.c", c.as_str())];
        let (result, sample) = scaling_sample(size, || verify_c_sources(&source, &sources));
        result.expect("a consuming call with many inputs verifies");
        samples.push(sample);
    }
    assert_near_linear_scaling_at_sampled_sizes("consuming call bound", &samples);
}

/// A loop's exit carries out the points its leaving pass recorded, read by
/// walking the path's change history back to a mark taken where the pass
/// began. The walk costs the changes the pass made: it is flat as the history
/// before the pass grows, and grows with the points the pass recorded.
#[test]
fn a_loop_exit_reads_only_the_points_its_pass_recorded() {
    use crate::instrumentation::measure_deterministic_work;
    let region = |index: usize, kind: ProgramPointKind| {
        ProgramPointSelector::ProgramPoint(ProgramPointRef {
            region: CodeRegionRef::Region(index),
            kind,
        })
    };
    let pass_work = |before: usize, during: usize| {
        let mut retained_states = RecordedStates::new();
        for index in 0..before {
            retained_states.insert(
                region(index, ProgramPointKind::Entry),
                ExecutionState::new(),
            );
        }
        let mark = retained_states.history_mark();
        for index in 0..during {
            retained_states.insert(
                region(before + index, ProgramPointKind::Exit),
                ExecutionState::new(),
            );
        }
        let (points, work) = measure_deterministic_work(|| retained_states.recorded_since(&mark));
        assert_eq!(points.retained_states.len(), during);
        work
    };
    let unrelated = [16_usize, 64, 256, 1024].map(|before| pass_work(before, 4));
    assert!(
        unrelated.iter().all(|work| *work == unrelated[0]),
        "the walk must not read history from before the pass: {unrelated:?}"
    );
    let related = [2_usize, 4, 8, 16].map(|during| pass_work(64, during));
    for pair in related.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3,
            "the walk must grow linearly with the pass's points: {related:?}"
        );
    }
}

/// A call inside an expression is its own step, and its result lives in the
/// path state only until the statement that reads it: checking `n` such
/// statements is work linear in `n`, with no result carried past its
/// statement.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn nested_call_results_scale_with_the_statements_that_read_them() {
    use crate::instrumentation::measure_deterministic_work;
    let sidecar = "verifying \"probe.c\";
        extern int32 id(int32 v) { ensures result == v; }
        int32 f(int32 x) { ensures result == result; }";
    let mut samples = Vec::new();
    for size in [8, 16, 32] {
        let body = "    x = id(x) ^ 1;\n".repeat(size);
        let program = format!("int id(int v);\nint f(int x) {{\n{body}    return x;\n}}\n");
        let (result, work) = measure_deterministic_work(|| {
            verify_c_sources(sidecar, &[("probe.c", program.as_str())])
        });
        result.expect("each call step's result is read by its own statement");
        samples.push((size, work));
    }
    let per_statement = |(size, work): (usize, usize)| work / size;
    let smallest = per_statement(samples[0]);
    assert!(
        samples
            .iter()
            .all(|sample| per_statement(*sample) <= smallest * 3 / 2),
        "nested call results grew per statement: {samples:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5.6s selected-guard context scaling audit"]
fn ordinary_fold_unfold_checks_only_selected_guards() {
    let mut samples = Vec::new();
    for size in [4, 16, 64, 256] {
        let facts = (0..size)
            .map(|index| format!("requires unrelated({index});\n"))
            .collect::<String>();
        let source = format!(
            r#"
predicate unrelated(n: int32) {{ n >= 0 }}
function tally(lo: int32, hi: int32) -> Integer {{
    (lo..hi).fold(0, |acc, k| {{ acc + 1 }})
}}
theorem append_tally(lo: int32, hi: int32) {{
    {facts}
    requires 0 <= lo;
    requires lo < hi;
    ensures tally(lo, hi) == tally(lo, hi - 1) + 1 by {{
        unfold(tally(lo, hi));
        close();
    }}
}}
"#
        );
        let (result, work) =
            crate::instrumentation::collect_tactic_work(|| verify_click_theorems(&source));
        result.unwrap();
        let unfold = work
            .iter()
            .find(|sample| sample.tactic.tactic_name == "unfold")
            .expect("the selected unfolding ran")
            .work;
        samples.push((size, unfold));
    }
    let baseline = samples[0].1;
    assert!(
        samples.iter().all(|(_, work)| *work <= baseline * 2 + 64),
        "unrelated facts grew selected fold checking: {samples:?}"
    );
}

/// A throwing call returns its selected memory input without walking the
/// unrelated function declarations or pure requirements at its call frontier.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: exceptional memory context scaling"]
fn exceptional_borrowed_memory_is_indexed_in_unrelated_context() {
    const CALL_WORK: &str = "operation `verification statement: call`";
    let mut samples = Vec::new();
    let mut frontier = Vec::new();
    for size in [2, 8, 16] {
        let mut c = String::from("void update(int32* value) { *value = 7; }\n");
        let mut source = String::from(
            "verifying \"memory.c\";\nfunction unrelated_fact(n: int32) -> int32 { n }\nvoid update(int32* value) throws int32 { owns value[0]; ensures value[0] == 7; exceptional ensures value[0] == 9; }\n",
        );
        for index in 0..size {
            c.push_str(&format!("int32 unused_{index}(int32 x) {{ return x; }}\n"));
            source.push_str(&format!(
                "int32 unused_{index}(int32 x) {{ ensures result == x; }}\n"
            ));
        }
        c.push_str("void target(int32* value) { update(value); }\n");
        source.push_str("void target(int32* value) throws int32 { owns value[0];\n");
        for index in 0..size {
            source.push_str(&format!(
                "requires unrelated_fact({}) != 0;\n",
                10000 + index
            ));
        }
        source.push_str("ensures value[0] == 7; exceptional ensures value[0] == 9; }\n");
        let (verified, sample) =
            scaling_sample(size, || verify_c_sources(&source, &[("memory.c", &c)]));
        verified.unwrap_or_else(|error| panic!("size {size}: {}", error.message()));
        frontier.push(sample.named_work.get(CALL_WORK).copied().unwrap_or(0));
        samples.push(sample);
    }
    assert_near_linear_scaling_at_sampled_sizes("exceptional borrowed memory", &samples);
    assert!(
        frontier[0] > 0 && frontier.iter().all(|work| *work == frontier[0]),
        "call frontier {frontier:?}"
    );
}

#[test]
fn recorded_call_snapshots_read_one_point_and_one_call() {
    for count in [8, 128, 1024] {
        let mut points = RecordedStates::new();
        let selected = ProgramPointSelector::Mark("saved".into());
        for region in 0..count {
            points.record_call_result(region, Some(crate::kernel::int32(region as u32)));
        }
        points.set_call_result_snapshot(&selected, Some(points.call_results.clone()));
        // Grow both the number of snapshots and the number of times the
        // selected call ran without changing its earlier snapshot.
        for run in 0..count {
            points.record_call_result(0, Some(crate::kernel::int32(1 + run as u32)));
            let point = ProgramPointSelector::Mark(format!("run_{run}"));
            points.set_call_result_snapshot(&point, Some(points.call_results.clone()));
        }
        assert_eq!(points.call_result_snapshots.len(), count + 1);
        let (saved, work) = crate::instrumentation::measure_deterministic_work(|| {
            points.call_results_at(&selected).unwrap().get(&0).cloned()
        });
        assert_eq!(
            saved.map(RetainedProgramValue::into_native_compat),
            Some(crate::kernel::int32(0))
        );
        assert_eq!(work, 1, "{count} calls and snapshots");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3.3s in the parallel gate"]
fn have_at_frontier_shares_the_context_across_call_history() {
    use crate::instrumentation::{VerificationEvent, collect};

    let samples = [4, 16, 64, 128].map(|calls| {
        let call_statements = "    touch();\n".repeat(calls);
        let c = format!(
            "int32 g[256];\nvoid touch() {{ g[255] = 1; }}\nint32 probe() {{\n    int32 x;\n{call_statements}    x = g[0];\n    return 0;\n}}"
        );
        let steps = "    step();\n".repeat(calls);
        let source = format!(
            r#"verifying "probe.c";
void touch() {{ owns g[255..256]; }}
int32 probe() {{
    owns g[0..256];
}} by {{
{steps}    mark before;
    step();
    mark after;
    have 0 != 255 by {{ close(); }}
    have separate(memory(g[255]), memory(g[0])) by {{
        apply(click::separation::separate_elements(g, 255, 0));
    }}
    have separate(statement({calls}).footprint, memory(g[0])) by {{
        close();
    }}
    have at(after, g[0]) == at(before, g[0]) by {{
        preserve(memory(g[0]), statement({calls}));
    }}
    step();
    step();
}}
"#
        );
        let (verified, events) = collect(|| verify_c_sources(&source, &[("probe.c", &c)]));
        verified.unwrap_or_else(|error| panic!("after {calls} calls: {}", error.message()));
        let work = events
            .into_iter()
            .filter_map(|event| match event {
                VerificationEvent::TacticFinished { tactic, work, .. }
                    if tactic.tactic_name == "have" && tactic.claim == "probe.contract" =>
                {
                    Some(work)
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        let work: [usize; 4] = work.try_into().expect("four explicit have scopes");
        work
    });
    eprintln!("frontier have work at 4, 16, 64, 128 calls: {samples:?}");
    assert!(samples.iter().all(|work| work[0] == samples[0][0]));
    assert!(
        samples
            .iter()
            .all(|work| work[1].abs_diff(samples[0][1]) <= 1)
    );
    assert!(samples.iter().all(|work| work[2] == samples[0][2]));
    // The last goal checks that an explicit preservation proof still works.
    // Naming its two historical reads has a separate version-walk cost.
}

fn check_struct_value_equality_cost(fields: usize) {
    use crate::instrumentation::measure_deterministic_work;
    // `*dst == *src` is its fields' equalities: forming the two values and
    // comparing them is linear in the fields, as writing the comparisons
    // out is.
    verify_c_sources("theorem warm() { ensures true by close(); }", &[]).unwrap();
    let names = (0..fields).map(|i| format!("f{i}")).collect::<Vec<_>>();
    let declaration = names
        .iter()
        .map(|name| format!("int32 {name};"))
        .collect::<String>();
    let copies = names
        .iter()
        .map(|name| format!("dst->{name} = src->{name};"))
        .collect::<String>();
    let program = format!(
        "struct wide {{ {declaration} }}; void copy(struct wide* dst, const struct wide* src) {{ {copies} }}"
    );
    let written = names
        .iter()
        .map(|name| format!("dst->{name} == src->{name}"))
        .collect::<Vec<_>>()
        .join(" and ");
    let mut pair = Vec::new();
    for claim in ["*dst == *src".to_string(), written] {
        let source = format!(
            "verifying \"probe.c\"; void copy(struct wide* dst, const struct wide* src) {{ owns *dst; views *src; requires separate(memory(*dst), memory(*src)); ensures {claim}; }}"
        );
        let (result, work) = measure_deterministic_work(|| {
            verify_c_sources(&source, &[("probe.c", program.as_str())])
        });
        result.unwrap_or_else(|error| panic!("{fields} fields: {}", error.message()));
        pair.push(work);
    }
    assert!(
        pair[0] <= pair[1] * 2,
        "struct value equality over {fields} fields: {pair:?}"
    );
    eprintln!("struct value equality work over {fields} fields (value, written): {pair:?}");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn struct_value_equality_costs_what_its_two_field_equalities_cost() {
    check_struct_value_equality_cost(2);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 7.9s in the parallel gate"]
fn struct_value_equality_costs_what_its_four_field_equalities_cost() {
    check_struct_value_equality_cost(4);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 16s in the parallel gate"]
fn struct_value_equality_costs_what_its_six_field_equalities_cost() {
    check_struct_value_equality_cost(6);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 10s in the parallel gate"]
fn struct_copy_field_equalities_expand_and_replay() {
    let program = r#"
        struct frame_record { int32 f0; int32 f1; int32 f2; int32 f3; };
        void copy_frame(struct frame_record* dst, const struct frame_record* src) {
            dst->f0 = src->f0;
            dst->f1 = src->f1;
            dst->f2 = src->f2;
            dst->f3 = src->f3;
        }
    "#;
    let sources = [("copy_frame.c", program)];
    for claim in [
        "*dst == *src",
        "dst->f0 == src->f0 and dst->f1 == src->f1 and dst->f2 == src->f2 and dst->f3 == src->f3",
    ] {
        let source = format!(
            r#"verifying "copy_frame.c";
            void copy_frame(struct frame_record* dst, const struct frame_record* src) {{
                owns *dst;
                views *src;
                requires separate(memory(*dst), memory(*src));
                ensures {claim};
            }}"#
        );
        let expanded = expand_c_claim_source_by_label(&source, &sources, "copy_frame.contract")
            .unwrap_or_else(|error| panic!("{claim}: {}", error.report()));
        crate::surface::without_implicit_solve_for_claim("copy_frame.contract", || {
            verify_c_sources(&expanded, &sources).map_err(|error| error.report())
        })
        .unwrap_or_else(|error| panic!("{claim}: {error}"));
    }
}
