use super::*;

#[test]
#[ignore = "nightly: source-level store proofs across context sizes"]
fn indexed_store_bounds_preparation_ignores_order_chain_length() {
    let mut samples = Vec::new();
    let mut solver_samples = Vec::new();
    for related in [false, true] {
        for size in [16, 31, 32, 64] {
            let parameters = (1..=size)
                .map(|i| format!(", int32 x{i}"))
                .collect::<String>();
            let chain_start = if related { 0 } else { 1 };
            let mut bounds = (chain_start..size)
                .map(|i| format!("requires x{i} < x{};\n", i + 1))
                .collect::<String>();
            if related {
                bounds.push_str(&format!("requires x{size} < len;"));
            }
            let c = format!(
                "void set(int32* data, int32 len, int32 x0{parameters}) {{ data[x0] = 100; return; }}"
            );
            let click = format!(
                r#"verifying "store.c";
void set(int32* data, int32 len, int32 x0{parameters}) {{
    owns data[0..len];
    requires 0 <= x0;
    {bounds}
}} by {{ step(); step(); }}"#
            );
            let (result, events) = crate::instrumentation::collect(|| {
                crate::surface::without_implicit_solve(|| {
                    verify_c_sources(&click, &[("store.c", &c)])
                })
            });
            let refusal = result.err().expect("the store needs a bounds proof");
            assert!(
                refusal.report().contains("0 <= x0 and x0 < len"),
                "related={related}, size={size}: {refusal}"
            );
            let work = events
                .iter()
                .filter_map(|event| match event {
                    crate::instrumentation::VerificationEvent::OperationFinished {
                        name,
                        work,
                        ..
                    } if name == "verification statement: store" => Some(*work),
                    _ => None,
                })
                .collect::<Vec<_>>();
            let [work] = work.as_slice() else {
                panic!("expected one store preparation at size {size}: {work:?}");
            };
            samples.push((related, size, *work));

            if related {
                let sources = [("store.c", c.as_str())];
                let (result, events) =
                    crate::instrumentation::collect(|| verify_c_sources(&click, &sources));
                result.unwrap_or_else(|error| panic!("size {size}: {error}"));
                let solver_work = events
                    .iter()
                    .find_map(|event| match event {
                        crate::instrumentation::VerificationEvent::TacticFinished {
                            tactic,
                            work,
                            ..
                        } if tactic.tactic_name == "implicit closer"
                            && tactic.source_index == 0 =>
                        {
                            Some(*work)
                        }
                        _ => None,
                    })
                    .expect("the store has an implicit bounds proof");
                solver_samples.push((size, solver_work));

                if size == 64 {
                    let expanded = expand_function_proof_source(&click, &sources, "set").unwrap();
                    assert!(expanded.contains("normalize() using"), "{expanded}");
                    crate::surface::without_implicit_solve(|| {
                        verify_c_sources(&expanded, &sources)
                    })
                    .unwrap();
                    let missing_link = expanded.replace("requires x32 < x33;\n", "");
                    assert_ne!(expanded, missing_link);
                    assert!(
                        crate::surface::without_implicit_solve(|| {
                            verify_c_sources(&missing_link, &sources)
                        })
                        .is_err()
                    );
                }
            }
        }
    }
    eprintln!("indexed store preparation: {samples:?}");
    assert!(
        samples.iter().all(|(_, _, work)| *work < samples[0].2 * 2),
        "{samples:?}"
    );
    eprintln!("indexed store bounds solver: {solver_samples:?}");
    assert!(
        solver_samples
            .iter()
            .all(|(size, work)| *work < 1000 * (size + 10)),
        "{solver_samples:?}"
    );
}

#[test]
fn explicit_adjacent_pointer_frames_compose_without_history_search() {
    let mut samples = Vec::new();
    for size in [2, 4, 8, 16, 32] {
        let mut c =
            String::from("struct job { int *output; }; void write(struct job *job, int *dest) {\n");
        let mut click = String::from(
            r#"
verifying "probe.c";
void write(struct job *job, int32 *dest) {
    views job->output;
    owns dest[0..1];
    requires separate(memory(job->output), memory(dest[0..1]));
    ensures job->output == old(job->output);
} by {
    mark entry;
"#,
        );
        for index in 0..size {
            c.push_str(&format!("*dest = {index};\n"));
            click.push_str(&format!(
                r#"
    mark before_{index};
    step() by {{ known(); }}
    mark after_{index};
    have job->output == at(before_{index}, job->output) by {{
        have separate(statement({index}).footprint, memory(job->output)) by {{
            normalize() using {{ at(entry, separate(memory(job->output), memory(dest[0..1]))); }};
        }}
        preserve(memory(job->output), statement({index}));
    }}
"#
            ));
            if index > 0 {
                click.push_str(&format!(
                    r#"
    have job->output == at(entry, job->output) by {{
        rewrite(job->output, at(before_{index}, job->output));
        known();
    }}
"#
                ));
            }
        }
        c.push_str("}\n");
        click.push_str("step();\nknown(); known();\nknown(); known(); known();\n}\n");
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::surface::without_implicit_solve(|| verify_c_sources(&click, &[("probe.c", &c)]))
        });
        result.unwrap_or_else(|error| panic!("size {size}: {error}\n{click}"));
        if size != 2 {
            samples.push((size, work));
        }
    }
    eprintln!("Surface explicit pointer frames: {samples:?}");
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 3, "{samples:?}");
    }
}

/// Obligation discovery must retain the call result, rather than applying all
/// postconditions a second time. Grow the selected contract as well as unrelated
/// input facts; count kernel executions and charged work, not wall time.
#[test]
#[ignore = "nightly: nine prepared-call proofs across contract and context sizes"]
fn prepared_call_obligations_execute_once_as_contract_and_context_grow() {
    for mode in ["bare", "by", "requires"] {
        let mut samples = Vec::new();
        for size in [1, 8, 32] {
            let conditions = (1..=size)
                .map(|n| format!("ensures result != -{n};\n"))
                .collect::<String>();
            let ambient = (1..=size)
                .map(|n| format!("requires unrelated != -{n};\n"))
                .collect::<String>();
            let body = "have positive(a) == 1 by { unfold(positive(a)); normalize() using { a > 0; }; } known();";
            let step = if mode == "bare" {
                "step();".to_string()
            } else if mode == "by" {
                format!("step() by {{ {body} }}")
            } else {
                format!("step() {{ requires positive(a) == 1 by {{ {body} }} }}")
            };
            let source = format!(
                r#"
verifying "call.c";
function positive(x: int32) -> int32 {{ if x > 0 {{ 1 }} else {{ 0 }} }}
extern int32 callee(int32 x) {{
    requires positive(x) == 1;
    ensures result == x;
    {conditions}
}}
int32 caller(int32 a, int32 unrelated) {{
    requires a > 0;
    {ambient}
    ensures result == a;
}} by {{
    {step}
    have positive(a) == 1 by known();
    step(); solve();
}}
"#
            );
            let ((result, work), events) = crate::instrumentation::collect(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    verify_c_sources(
                        &source,
                        &[(
                            "call.c",
                            "int32 caller(int32 a, int32 unrelated) { return callee(a); }",
                        )],
                    )
                })
            });
            result.unwrap_or_else(|error| panic!("{mode}, {size}: {error}"));
            let applications = events
                .iter()
                .filter(|event| {
                    matches!(event,
                        crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                        if name == "verification statement: call"
                    )
                })
                .count();
            assert_eq!(
                applications, 1,
                "{mode}, {size}: a prepared call must not execute twice"
            );
            samples.push((size, work));
        }
        eprintln!("prepared {mode} call work: {samples:?}");
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 * pair[0].0 <= pair[0].1 * pair[1].0 * 2,
                "prepared-call work must remain near-linear: {samples:?}"
            );
        }
    }
}

#[test]
#[ignore = "nightly: source-level obligation scaling through 512 premises"]
fn known_step_obligations_do_not_scan_unrelated_facts() {
    known_obligation_scaling("step", false);
}

#[test]
#[ignore = "nightly: source-level obligation scaling through 512 premises"]
fn known_step_obligations_do_not_scan_related_facts() {
    known_obligation_scaling("step", true);
}

#[test]
#[ignore = "nightly: source-level obligation scaling through 512 premises"]
fn known_fold_obligations_do_not_scan_unrelated_facts() {
    known_obligation_scaling("fold", false);
}

#[test]
#[ignore = "nightly: source-level obligation scaling through 512 premises"]
fn known_fold_obligations_do_not_scan_related_facts() {
    known_obligation_scaling("fold", true);
}

fn known_obligation_scaling(tactic: &str, related: bool) {
    let mut samples = Vec::new();
    for size in [8, 32, 128, 512] {
        let variable = if related { "x" } else { "y" };
        let ambient = (0..size)
            .map(|i| format!("requires {variable} < {};", 100 + i))
            .collect::<String>();
        let (body, produces, operation) = if tactic == "step" {
            ("needs(x);", "", "step() by { known(); }")
        } else {
            (
                "",
                "produces positive(x);",
                "fold(positive(x)) by { known(); }",
            )
        };
        let c = format!("void needs(int32 x) {{}} void check(int32 x, int32 y) {{{body}}}");
        let click = format!(
            r#"
verifying "known.c";
resource positive(x: int32) {{ fact x > 0; }}
void needs(int32 x) {{ requires x > 0; ensures 1 == 1; }}
void check(int32 x, int32 y) {{ requires x > 0; {ambient} {produces} ensures 1 == 1; }} by {{
    {operation}
    step_until(function.exit);
    solve();
}}
"#
        );
        let (result, work) = crate::instrumentation::collect_tactic_work(|| {
            verify_c_sources(&click, &[("known.c", &c)])
        });
        result.unwrap_or_else(|error| panic!("{tactic}, related={related}, size={size}: {error}"));
        let selected = work
            .iter()
            // Both written `by` forms are represented by StepProved.
            .filter(|sample| {
                sample.tactic.claim == "check.contract" && sample.tactic.tactic_index == 0
            })
            .map(|sample| sample.work)
            .max()
            .expect("selected tactic work");
        samples.push(selected);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 128),
        "{tactic}, related={related}: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: named fold source selection through 512 resource arms"]
fn named_fold_obligation_source_selects_only_its_arm() {
    let mut samples = Vec::new();
    for size in [8, 32, 128, 512] {
        let variants = (0..size)
            .map(|i| format!("V{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let arms = (0..size)
            .map(|i| format!("Choice::V{i} => {{ owns p[0..1]; fact p[0] == 0; }},"))
            .collect::<String>();
        let source = format!(
            r#"
verifying "fold.c";
spec enum Choice {{ {variants} }}
resource cell(p: int32*) {{ field tag: Choice; match tag {{ {arms} }} }}
void pack(int32* p) {{
    consumes p[0..1];
    requires p[0] == 0;
    produces owner: cell(p);
}} by {{
    let owner = fold(cell(p), {{ tag: Choice::V0 }});
}}
"#
        );
        let (result, work) = crate::instrumentation::collect_tactic_work(|| {
            verify_c_sources(&source, &[("fold.c", "void pack(int32* p) {}")])
        });
        result.unwrap_or_else(|error| panic!("{size}: {error}"));
        let selected = work
            .iter()
            .filter(|sample| {
                sample.tactic.claim == "pack.contract" && sample.tactic.tactic_index == 0
            })
            .map(|sample| sample.work)
            .max()
            .expect("fold work");
        samples.push(selected);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 64),
        "{samples:?}"
    );
}

#[test]
#[ignore = "nightly: three fold preparation forms"]
fn prepared_named_fold_constructs_once() {
    for suffix in [";", " by { known(); }", " { requires x > 0 by known(); }"] {
        let source = format!(
            r#"
verifying "fold.c";
resource positive(x: int32) {{ field value: int32; fact value > 0; }}
void make(int32 x) {{ requires x > 0; produces p: positive(x); }} by {{
    let p = fold(positive(x), {{ value: x }}){suffix}
}}
"#
        );
        let (result, events) = crate::instrumentation::collect(|| {
            verify_c_sources(&source, &[("fold.c", "void make(int32 x) {}")])
        });
        result.unwrap_or_else(|error| panic!("{suffix}: {error}"));
        let constructions = events
            .iter()
            .filter(|event| {
                matches!(event,
                    crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                        if name == "resource fold: construct selected instance"
                )
            })
            .count();
        assert_eq!(
            constructions, 1,
            "{suffix}: completing obligations must not reconstruct the fold"
        );
    }
}

#[test]
#[ignore = "nightly: prepared folds after growing execution histories"]
fn prepared_named_fold_completion_does_not_walk_history() {
    let mut samples = Vec::new();
    for size in [1, 8, 32] {
        let statements = "scratch = 0;\n".repeat(size);
        let steps = "step();\n".repeat(size + 1);
        let source = format!(
            r#"
verifying "fold.c";
function positive(x: int32) -> int32 {{ if x > 0 {{ 1 }} else {{ 0 }} }}
resource positive_value(x: int32) {{ field value: int32; fact positive(value) == 1; }}
void make(int32 x) {{ requires x > 0; produces p: positive_value(x); }} by {{
    {steps}
    let p = fold(positive_value(x), {{ value: x }}) by {{
        have positive(x) == 1 by {{ unfold(positive(x)); normalize() using {{ x > 0; }}; }}
        known();
    }}
    have positive(x) == 1 by known();
    step(); solve();
}}
"#
        );
        let c = format!("void make(int32 x) {{ int scratch; {statements} }}");
        let (result, events) =
            crate::instrumentation::collect(|| verify_c_sources(&source, &[("fold.c", &c)]));
        result.unwrap_or_else(|error| panic!("size {size}: {error}"));
        let completions = events
            .iter()
            .filter_map(|event| match event {
                crate::instrumentation::VerificationEvent::OperationFinished {
                    name, work, ..
                } if name == "resource fold: finish prepared instance" => Some(*work),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(completions.len(), 1, "size {size}: {completions:?}");
        samples.push(completions[0]);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 16),
        "{samples:?}"
    );
}

#[test]
#[ignore = "nightly: return-fold construction and history controls"]
fn prepared_return_fold_constructs_once_without_recovering_history() {
    let mut samples = Vec::new();
    for count in [1, 8, 32] {
        let facts = "have x == x by { normalize(); }\n".repeat(count);
        let source = format!(
            r#"
verifying "fold.c";
resource positive(x: int32) {{ field value: int32; fact value > 0; }}
void make(int32 x) {{ requires x > 0; produces p: positive(x); }} by {{
    step_until(function.exit);
    {facts}
    let p = fold(positive(x), {{ value: x }}) by {{ known(); }}
}}
"#
        );
        let (result, events) = crate::instrumentation::collect(|| {
            verify_c_sources(&source, &[("fold.c", "void make(int32 x) {}")])
        });
        result.unwrap_or_else(|error| panic!("{count}: {error}"));
        let mut constructions = 0;
        let mut recovery = 0;
        for event in events {
            if let crate::instrumentation::VerificationEvent::OperationFinished {
                name, work, ..
            } = event
            {
                if name == "return fold: construct selected instance" {
                    constructions += 1;
                }
                if name == "return fold: recover state" {
                    recovery += work;
                }
            }
        }
        eprintln!(
            "return fold: {count} preceding proofs, {constructions} constructions, {recovery} recovery work"
        );
        samples.push((count, constructions, recovery));
    }
    assert!(
        samples
            .iter()
            .all(|(_, constructions, recovery)| *constructions == 1 && *recovery <= 8),
        "{samples:?}"
    );
}

#[test]
#[ignore = "nightly: population fold construction and history controls"]
fn prepared_population_fold_constructs_once() {
    let mut samples = Vec::new();
    for named in [true, false] {
        for returned in [false, true] {
            for count in [1, 8, 32] {
                let history = "have x == x by { normalize(); }\n".repeat(count);
                let before = if returned {
                    "step_until(function.exit);"
                } else {
                    ""
                };
                let after = if returned {
                    ""
                } else {
                    "step_until(function.exit);"
                };
                let source = format!(
                    r#"
verifying "fold.c";
authorized resource ticket(p: int32*) {{ field serial: int32; }}
resource control(p: int32*, x: int32) {{
    field value: int32;
    owns authority(ticket(p));
    fact value > 0;
}}
void make(int32* p, int32 x) {{
    owns authority(ticket(p));
    owns witness: ticket(p);
    requires x > 0;
}} by {{
    {before}
    {history}
    let c = fold(control(p, x), {{ value: x }}) by {{ known(); }}
    unfold(c);
    {after}
    solve();
}}
"#
                );
                let source = if named {
                    source
                } else {
                    let history = history.replace("x == x", "pool == pool");
                    format!(
                        r#"
verifying "fold.c";
authorized resource slot(pool: struct pool*) {{}}
resource control(pool: struct pool*) {{
    owns *pool;
    owns authority(slot(pool));
    fact pool->capacity == count(slot(pool));
}}
void make(struct pool* pool) {{
    owns control(pool);
    owns pool->capacity of slot(pool);
}} by {{
    unfold(control(pool));
    {before}
    {history}
    fold(control(pool)) by {{ solve(); }}
    {after}
    solve();
}}
"#
                    )
                };
                let c = if named {
                    "void make(int32* p, int32 x) {}"
                } else {
                    "struct pool { int32 capacity; }; void make(struct pool* pool) {}"
                };
                let sources = [("fold.c", c)];
                let (result, events) =
                    crate::instrumentation::collect(|| verify_c_sources(&source, &sources));
                result.unwrap_or_else(|e| {
                    panic!("named={named}, returned={returned}, count={count}: {e}")
                });
                let constructions = events
                .iter()
                .filter(|event| {
                    matches!(event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == if named { "resource instance: construct fold" } else { "resource fold: apply selected fold" })
                })
                .count();
                samples.push((named, returned, count, constructions));
                if count == 1 {
                    for source in [
                        source.clone(),
                        source
                            .replace(" by { known(); }", ";")
                            .replace(" by { solve(); }", ";"),
                    ] {
                        let expanded =
                            expand_function_proof_source(&source, &sources, "make").unwrap();
                        without_implicit_solve_for_claim("make.contract", || {
                            verify_c_sources(&expanded, &sources).map_err(|error| error.report())
                        })
                        .unwrap();
                        if named {
                            assert!(
                                verify_c_sources(&source.replace("requires x > 0;", ""), &sources)
                                    .is_err(),
                                "a proposed population fold cannot supply its own body premise"
                            );
                            assert!(
                                verify_c_sources(
                                    &source.replacen(
                                        "    owns authority(ticket(p));\n    owns witness",
                                        "    owns witness",
                                        1
                                    ),
                                    &sources
                                )
                                .is_err(),
                                "a population fold needs its authority"
                            );
                        }
                    }
                }
            }
        }
    }
    eprintln!("population fold constructions: {samples:?}");
    assert!(samples.iter().all(|(_, _, _, n)| *n == 1), "{samples:?}");
}

#[test]
#[ignore = "nightly: legacy outcome fold preparation and replay"]
fn prepared_legacy_outcome_fold_applies_once() {
    let mut samples = Vec::new();
    for opaque in [false, true] {
        for size in [1, 8, 32] {
            let history = "have x == x by { normalize(); }\n".repeat(size);
            let source = format!(
                r#"
verifying "legacy.c";
resource positive(x: int32) {{ fact x > 0; }}
void make(int32 x) {{ requires x > 0; produces positive(x); }} by {{
    step_until(function.exit);
    {history}
    fold(positive(x)) by {{ known(); }}
    solve();
}}
"#
            );
            let source = if opaque {
                source.replace("resource positive", "predicate positive_value(x: int32) { x > 0 }\nresource positive")
                .replace("fact x > 0;", "fact positive_value(x);")
                .replace("by { known(); }", "by { have positive_value(x) by { unfold(positive_value(x)); known(); } known(); }")
            } else {
                source
            };
            let sources = [("legacy.c", "void make(int32 x) {}")];
            let (result, events) =
                crate::instrumentation::collect(|| verify_c_sources(&source, &sources));
            result.unwrap();
            let count = events
                .iter()
                .filter(|event| {
                    matches!(event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
            if name == "resource fold: apply selected fold")
                })
                .count();
            samples.push((opaque, size, count));
            if size == 1 {
                let expanded = expand_function_proof_source(&source, &sources, "make").unwrap();
                without_implicit_solve_for_claim("make.contract", || {
                    verify_c_sources(&expanded, &sources).map_err(|e| e.report())
                })
                .unwrap();
                assert!(
                    verify_c_sources(&source.replace("requires x > 0;", ""), &sources).is_err()
                );
            }
        }
    }
    eprintln!("legacy outcome fold applications: {samples:?}");
    assert!(samples.iter().all(|(_, _, n)| *n == 1), "{samples:?}");
}

#[test]
#[ignore = "nightly: loan-backed call preparation and replay"]
fn prepared_view_call_does_not_retry_loan_recovery() {
    let mut samples = Vec::new();
    for callback in [false, true] {
        for size in [1, 8, 32] {
            let history = "have a == a by { normalize(); }\n".repeat(size);
            let source = format!(
                r#"
verifying "call.c";
extern int32 read(int32 x, int32* p) {{
    views *p;
    requires x > 0;
    ensures result == x;
}}
int32 caller(int32 a, int32* p) {{
    owns *p;
    requires a > 0;
    ensures result == a;
}} by {{
    {history}
    step() by {{ known(); }}
    step(); solve();
}}
"#
            );
            let source = if callback {
                source
                    .replace("extern int32 read", "contract int32 Read")
                    .replace(
                        "int32 caller(int32 a, int32* p)",
                        "int32 caller(int32 (*f)(int32, int32*), int32 a, int32* p)",
                    )
                    .replace("    owns *p;", "    requires Read(f);\n    owns *p;")
                    .replace("step() by", "step(Read) by")
            } else {
                source
            };
            let c = if callback {
                "int32 caller(int32 (*f)(int32, int32*), int32 a, int32* p) { return f(a, p); }"
            } else {
                "int32 caller(int32 a, int32* p) { return read(a, p); }"
            };
            let sources = [("call.c", c)];
            let (result, events) =
                crate::instrumentation::collect(|| verify_c_sources(&source, &sources));
            result.unwrap();
            let calls = events
                .iter()
                .filter(|event| {
                    matches!(event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
            if name == "verification statement: call")
                })
                .count();
            samples.push((callback, size, calls));
            if size == 1 {
                let expanded = expand_function_proof_source(&source, &sources, "caller").unwrap();
                without_implicit_solve_for_claim("caller.contract", || {
                    verify_c_sources(&expanded, &sources).map_err(|e| e.report())
                })
                .unwrap();
                assert!(
                    verify_c_sources(&source.replace("requires a > 0;", ""), &sources).is_err()
                );
            }
        }
    }
    eprintln!("view call preparations: {samples:?}");
    assert!(samples.iter().all(|(_, _, n)| *n == 1), "{samples:?}");
}

#[test]
#[ignore = "nightly: guarded statement preparation and expansion replay"]
fn prepared_guarded_statement_does_not_retry_execution() {
    let mut samples = Vec::new();
    for assertion in [false, true] {
        for size in [1, 8, 32] {
            let history = "have x == x by { normalize(); }\n".repeat(size);
            let (c, contract, steps, operation) = if assertion {
                (
                    "int32 values[4]; int32 f(int32 x) { int32 r; r = values[x]; return r; }",
                    "owns values[0..4]; requires x == 1 or x == 2;",
                    "step(); step() { requires x >= 0 and x < 4 by { cases { x == 1 => { solve(); } x == 2 => { solve(); } } } } step(); step(); solve();",
                    "verification statement: assert",
                )
            } else {
                (
                    "int32 f(int32 x) { return x + 1; }",
                    "requires x == 5 or x == 7;",
                    "step() by { cases { x == 5 => { solve(); } x == 7 => { solve(); } } } solve();",
                    "verification statement: return",
                )
            };
            let source = format!(
                "verifying \"guard.c\";\nint32 f(int32 x) {{ {contract} ensures result == result; }} by {{ {history} {steps} }}"
            );
            let sources = [("guard.c", c)];
            let (result, events) =
                crate::instrumentation::collect(|| verify_c_sources(&source, &sources));
            result.unwrap_or_else(|e| panic!("assertion={assertion}: {e}"));
            let count = events.iter().filter(|event| matches!(event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. } if name == operation
            )).count();
            samples.push((assertion, size, count));
            if size == 1 {
                let expanded = expand_function_proof_source(&source, &sources, "f").unwrap();
                without_implicit_solve_for_claim("f.contract", || {
                    verify_c_sources(&expanded, &sources).map_err(|e| e.report())
                })
                .unwrap();
                let bad = source
                    .replace("requires x == 5 or x == 7;", "")
                    .replace("requires x == 1 or x == 2;", "");
                assert!(
                    verify_c_sources(&bad, &sources).is_err(),
                    "the retained arm cannot prove its own guard"
                );
            }
        }
    }
    eprintln!("guarded statement constructions: {samples:?}");
    assert!(samples.iter().all(|(_, _, n)| *n == 1), "{samples:?}");
}

#[test]
#[ignore = "focused audit: state-valued fold prerequisites expand and cold-replay"]
fn prepared_fold_state_pointer_reads_current_memory() {
    for element in ["int32", "uint8"] {
        let c = format!(
            "struct holder {{ {element}* data; }}; void make(struct holder* h) {{ h->data[0] = 1; }}"
        );
        let source = format!(
            r#"
verifying "fold.c";
resource cells(p: {element}*) {{
    field next: int32;
    owns p[0..1];
    fact 0 <= next;
    fact forall(k: int32) {{ next <= k and k < 1 implies p[k] == 1 }};
}}
void make(struct holder* h) {{
    views *h;
    consumes h->data[0..1];
    requires h->data[0] == 0;
    produces z: cells(old(h->data));
}} by {{
    step();
    let z = fold(cells(old(h->data)), {{next: 0}});
    step_until(function.exit);
    solve();
}}
"#
        );
        let sources = [("fold.c", c.as_str())];
        verify_c_sources(&source, &sources).unwrap();
        let expanded = expand_function_proof_source(&source, &sources, "make").unwrap();
        without_implicit_solve_for_claim("make.contract", || {
            verify_c_sources(&expanded, &sources).map_err(|error| error.report())
        })
        .unwrap();
        let wrong = source.replace("implies p[k] == 1", "implies p[k] == 0");
        assert!(verify_c_sources(&wrong, &sources).is_err());
    }
}

#[test]
#[ignore = "focused audit: arithmetic fold fields retain their type in expansion"]
fn prepared_fold_arithmetic_field_replays() {
    let source = r#"
verifying "fold.c";
resource cell(p: int32*) {
    field value: int32;
    owns *p;
    fact *p == value;
    fact 0 <= value;
}
void make(int32* p, int32 n) {
    consumes *p;
    requires 0 <= n and n <= 100;
    produces r: cell(p);
} by {
    step();
    let r = fold(cell(p), { value: n + 1 });
    step_until(function.exit);
    solve();
}
"#;
    let sources = [("fold.c", "void make(int32* p, int32 n) { *p = n + 1; }")];
    verify_c_sources(source, &sources).unwrap();
    let expanded = expand_function_proof_source(source, &sources, "make").unwrap();
    without_implicit_solve_for_claim("make.contract", || {
        verify_c_sources(&expanded, &sources).map_err(|error| error.report())
    })
    .unwrap();
}

/// The implicit tail proves a store's index disequality before the store, so
/// the store keeps the cell it would otherwise forget. Its search reads only
/// the cells the statement changed and solves at most a fixed number of
/// disequalities, so its work grows with unrelated stores and facts as the
/// statements themselves do. A miss, where the index may equal the cell's,
/// must stay as prompt: the false claim is refused at every size.
#[test]
fn store_index_separation_search_scales_with_unrelated_stores_and_facts() {
    store_index_separation_search_scales("int", "int32", "");
}

/// [`store_index_separation_search_scales_with_unrelated_stores_and_facts`]
/// with `size_t` indices: the store reads the `uint64` index-word
/// disequality, and the search proves `j != 0u64` the same way.
#[test]
#[ignore = "nightly: 2.6s; the int32 sibling runs in the gate"]
fn wide_store_index_separation_search_scales_with_unrelated_stores_and_facts() {
    store_index_separation_search_scales("size_t", "size_t", "u64");
}

fn store_index_separation_search_scales(c_index: &str, click_index: &str, suffix: &str) {
    for hit in [true, false] {
        let mut samples = Vec::new();
        for size in [2, 4, 8, 16] {
            let parameters = (0..size).map(|k| format!(", int x{k}")).collect::<String>();
            let stores = (0..size)
                .map(|k| format!("    b[{k}] = x{k};\n    q[{}] = {k};\n", k + 1))
                .collect::<String>();
            let c = format!(
                "#include <stddef.h>\n#include <stdlib.h>\nint read_first({c_index} m, {c_index} j{parameters}) {{\n    int b[{size}];\n    int *q = malloc(m * sizeof(int));\n    if (q == 0) {{\n        return 7;\n    }}\n    q[0] = 7;\n{stores}    q[j] = 1;\n    int r = q[0];\n    free(q);\n    return r;\n}}\n"
            );
            let click_parameters = (0..size)
                .map(|k| format!(", int32 x{k}"))
                .collect::<String>();
            let facts = (0..size)
                .map(|k| format!("    requires x{k} <= {k};\n"))
                .collect::<String>();
            let lower = if hit { 1 } else { 0 };
            let click = format!(
                "verifying \"probe.c\";\nint32 read_first({click_index} m, {click_index} j{click_parameters}) {{\n    requires {}{suffix} <= m;\n    requires m <= 1000{suffix};\n    requires {lower}{suffix} <= j;\n    requires j < m;\n{facts}    ensures result == 7;\n}}\n",
                size + 2
            );
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c_sources(&click, &[("probe.c", &c)])
            });
            match (hit, result) {
                (true, Err(error)) => panic!("size {size}: {}\n{click}\n{c}", error.report()),
                (false, Ok(_)) => panic!("size {size}: a store that may hit q[0] kept it"),
                _ => {}
            }
            // The first size also pays one-time setup.
            if size != 2 {
                samples.push((size, work));
            }
        }
        eprintln!("store index separation ({c_index}, hit: {hit}): {samples:?}");
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1 * 3,
                "{c_index}, hit: {hit}: {samples:?}"
            );
        }
    }
}

#[test]
fn direct_store_source_publication_ignores_rhs_depth() {
    check_word_store_source_publication("*p", "p[0]", "", "owns *p;");
}

#[test]
fn indexed_store_source_publication_ignores_rhs_depth() {
    check_word_store_source_publication("p[0]", "p[0]", "", "owns *p;");
    check_word_store_source_publication("p[1]", "p[1]", "", "owns p[0..4];");
    check_word_store_source_publication(
        "p[i]",
        "p[i]",
        "int32 i, ",
        "owns p[0..4]; requires 0 <= i; requires i < 4;",
    );
}

fn check_word_store_source_publication(
    lvalue: &str,
    reads: &str,
    index_parameter: &str,
    contract: &str,
) {
    use crate::instrumentation::VerificationEvent;

    let mut publication_work = Vec::new();
    for depth in [4, 16, 40] {
        let updates = "    x = x * 3u + 1u;\n".repeat(depth);
        let source = format!(
            "void set(uint32* p, {index_parameter}uint32 x) {{\n{updates}    {lvalue} = x;\n    x = x + 1u;\n}}"
        );
        let steps = "    step();\n".repeat(depth + 2);
        let equation =
            format!("at(statement({depth}).exit, {reads}) == at(statement({depth}).entry, x)");
        let click = format!(
            "verifying \"store.c\";\nvoid set(uint32* p, {index_parameter}uint32 x) {{ {contract} }} by {{\n{steps}    have {equation} by {{ known(); }}\n}}"
        );
        let sources = [("store.c", source.as_str())];
        let (result, events) =
            crate::instrumentation::collect(|| verify_c_sources(&click, &sources));
        result.unwrap_or_else(|error| panic!("{lvalue}, depth {depth}: {}", error.report()));
        let preparation = events
            .iter()
            .find_map(|event| match event {
                VerificationEvent::OperationFinished { name, work, .. }
                    if name == "verification statement: store" =>
                {
                    Some(*work)
                }
                _ => None,
            })
            .expect("the C store was executed");
        let step = events
            .iter()
            .find_map(|event| match event {
                VerificationEvent::TacticFinished { tactic, work, .. }
                    if tactic.tactic_name == "step" && tactic.source_index == depth =>
                {
                    Some(*work)
                }
                _ => None,
            })
            .expect("an explicit step executed the store");
        publication_work.push(step - preparation);

        if depth == 40 {
            let wrong = click.replace(
                &equation,
                &format!("at(statement({depth}).exit, {reads}) == x"),
            );
            assert!(verify_c_sources(&wrong, &sources).is_err());
        }
    }
    assert!(
        publication_work
            .iter()
            .all(|work| *work <= publication_work[0] + 36),
        "{lvalue} publication grew with RHS depth: {publication_work:?}"
    );
}

#[test]
fn repeated_unsigned_stores_keep_preparation_independent_of_rhs_depth() {
    use crate::instrumentation::VerificationEvent;
    let mut samples = Vec::new();
    for count in [8, 24, 48] {
        let body = "    p[0] = x; x = x * 3u + 1u;\n".repeat(count);
        let c = format!("void set(uint32* p, uint32 x) {{\n{body}}}");
        let steps = "    step();\n".repeat(2 * count);
        let last = 2 * count - 2;
        let click = format!(
            "verifying \"store.c\";\nvoid set(uint32* p, uint32 x) {{ owns *p; }} by {{\n{steps}\
             have at(statement({last}).exit, p[0]) == at(statement({last}).entry, x) by {{ known(); }}\n}}"
        );
        let (verified, events) = crate::instrumentation::collect(|| {
            verify_c_sources(&click, &[("store.c", c.as_str())])
        });
        verified.unwrap_or_else(|error| panic!("count {count}: {}", error.report()));
        let preparation = events
            .iter()
            .rev()
            .find_map(|event| match event {
                VerificationEvent::OperationFinished { name, work, .. }
                    if name == "verification statement: store" =>
                {
                    Some(*work)
                }
                _ => None,
            })
            .expect("the store was executed");
        let step = events
            .iter()
            .find_map(|event| match event {
                VerificationEvent::TacticFinished { tactic, work, .. }
                    if tactic.tactic_name == "step" && tactic.source_index == last =>
                {
                    Some(*work)
                }
                _ => None,
            })
            .expect("the last store stepped");
        samples.push((preparation, step));
    }
    assert!(
        samples
            .iter()
            .all(|&(preparation, step)| preparation <= samples[0].0 + 32
                && step <= samples[0].1 + 64),
        "a store grew with RHS depth: {samples:?}"
    );
}
