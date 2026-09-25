use super::*;

#[test]
fn execution_target_resource_scope_parsing_is_linear_in_selected_declarations() {
    let samples = [1, 8, 32, 128].map(|count| {
        let mut source = "resource Counter() { field revision: int32; }\n".to_string();
        for index in 0..count {
            source.push_str(&format!("theorem lift{index}(callback: int32 (*)()) executes callback() {{ requires C{index}(callback); ensures C{index}(callback) as {{ cell: k }} by {{ step(C{index}(k)); simp(); }} }}\n"));
        }
        for index in 0..count {
            source.push_str(&format!("contract C{index}(cell: Counter()) for int32() {{ owns cell; ensures result == 0; }}\n"));
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
fn nested_conjunction_body_parsing_uses_small_frames_and_linear_work() {
    std::thread::Builder::new()
        .name("small-stack-proof-body-parser".into())
        .stack_size(7 * 256 * 1024)
        .spawn(|| {
            let samples = [2, 4, 8, 16].map(|depth| {
                let mut body = "have 0 == 0 by { normalize(); } normalize();".to_string();
                for _ in 0..depth {
                    body = format!("both {{ {body} }} and {{ normalize(); }}");
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
            theorem nested_result(n: Nat) {{ ensures nested(n) == n by {{ unfold(nested(n)); normalize(); }} }}"
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
                 }} == value by {{ normalize(); }}\n\
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
             theorem nested() {{ ensures {body} == 0 by {{ normalize(); }} }}"
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
fn parametric_theorem_declarations_have_near_linear_checking_work() {
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let source = (0..size).map(|index| format!(
            "theorem reflexive_{index}<T>(x: T) {{ ensures x == x by {{ normalize(); }} }}\n"
        )).collect::<String>();
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
                            "theorem shared_false(x: int32) { ensures x == x + 1 by simp; }",
                            [],
                        ),
                        ClickModuleSource::new(
                            format!("entry_{index}.click"),
                            format!(
                                "import \"shared.click\"; theorem local_{index}(x: int32) {{ ensures x == x + 1 by {{ apply(shared_false(x)); assumption(); }} }}"
                            ),
                            ["shared.click".to_string()],
                        ),
                    ],
                );
                verify_c0_project(&project, &[])?;
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

/// Lowering a specification `if` folds a literally constant condition and
/// otherwise lowers both branches. It reads no ambient fact, so checking a
/// requirement that contains one must cost the same whatever else the caller
/// happens to know. The requirement here is a conditional the caller cannot
/// settle, which is the case a branch-deciding lowering would have searched
/// for.
#[test]
fn specification_conditional_lowering_ignores_unrelated_ambient_facts() {
    let mut samples = Vec::new();
    let mut requirement_work = Vec::new();
    for size in [8, 16, 32, 64] {
        let unrelated = (0..size)
            .map(|index| format!("    have 0 <= {index} by {{\n        normalize();\n    }}\n"))
            .collect::<String>();
        let click_source = format!(
            "verifying \"conditional_callee.c\";\n\
             verifying \"conditional_caller.c\";\n\
             \n\
             int32 conditional_callee(int32 flag, int32 left, int32 right) {{\n    \
                 requires (if flag != 0 {{ left }} else {{ right }}) == 7;\n    \
                 ensures result == 0;\n\
             }} by auto;\n\
             \n\
             int32 conditional_caller(int32 flag, int32 left, int32 right) {{\n    \
                 requires (if flag != 0 {{ left }} else {{ right }}) == 7;\n    \
                 ensures result == 0;\n\
             }} by {{\n{unrelated}    execute();\n    simp();\n}}\n"
        );
        let (verified, sample) = scaling_sample(size, || {
            verify_c0_sources(
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
fn verified_call_ensure_premises_ignore_unrelated_ambient_facts() {
    let mut samples = Vec::new();
    let mut ensure_work = Vec::new();
    for size in [8, 16, 32, 64] {
        let unrelated = (0..size)
            .map(|index| {
                format!(
                    "    have {index} <= count + {index} by {{\n        \
                     arithmetic() using {{\n            0 <= count;\n            \
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
                 if flag > 0 {{\n        execute();\n        simp();\n    \
                 }} else {{\n        execute();\n        simp();\n    }}\n\
             }}\n\
             \n\
             int32 ensure_premise_scaling_caller(int32 count, int32* cell) {{\n    \
                 requires 0 <= count;\n    \
                 requires count <= 1000;\n    \
                 owns cell[0..1];\n    \
                 ensures result == 0;\n\
             }} by {{\n{unrelated}    execute();\n    simp();\n}}\n"
        );
        let (verified, sample) = scaling_sample(size, || {
            verify_c0_sources(
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
            "consumes data[0..length];\n    produces data[0..length];",
            2 * statement_count,
        ),
    };
    let mut click_source = format!(
        "verifying \"load_line.c\";\n\nint32 load_line(int32 data[], int32 length) {{\n    requires {statement_count} <= length;\n    requires 2 <= length;\n    requires ((uint32)length) <= 1073741823u32;\n    {permission}\n    ensures result == data[{last}];\n}} by {{\n"
    );
    let statement_count = statements;
    for _ in 0..=statement_count + 1 {
        click_source.push_str("    step();\n");
    }
    click_source.push_str("    normalize();\n");
    if matches!(axis, LoadAxis::OneCellAcrossStores) {
        // The `produces` claim has no simple closer and takes the one smart
        // tactic in this fixture.
        click_source.push_str("    simp();\n");
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
        "}\n\nverifying \"preserve_bundle.c\";\n\nint32 preserve_bundle(int32 p[]) {\n    views bundle(p);\n    ensures result == 0;\n} by {\n    step();\n    simp();\n}\n",
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
fn straight_line_proof_steps_scale_near_linearly_with_retained_snapshots() {
    for snapshot_claim in [false, true] {
        let mut finalization_views = Vec::new();
        let samples = [8, 16, 32, 64]
            .into_iter()
            .map(|size| {
                let (c_source, click_source) = straight_line_project(size, snapshot_claim);
                let ((verified, view_count), sample) = scaling_sample(size, || {
                    proof::count_finalization_view_constructions(|| {
                        verify_c0_sources(&click_source, &[("straight.c", c_source.as_str())])
                    })
                });
                verified.unwrap_or_else(|error| {
                    panic!(
                        "size {size} straight-line fixture (snapshot={snapshot_claim}) failed: {}",
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
            let (c_source, click_source) =
                function_with_unrelated_facts(size, "    step();\n    assumption();\n");
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
                "    step();\n    transport(target == 7, result == 7) using {\n        target == 7;\n    }\n    assumption();\n",
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
fn composite_definition_members_preserve_small_bundle() {
    let (c_source, click_source) = resource_member_project(3);
    let verified = verify_c0_sources(&click_source, &[("preserve_bundle.c", c_source.as_str())])
        .expect("a small composite resource bundle should verify");
    assert!(!verified.is_empty());
}

#[test]
fn composite_definition_members_keep_separation_work_compact() {
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

/// The change history is one node per recorded snapshot. Dropping a long
/// history through the derived `Drop` recursed once per node and overflowed
/// `click verify`'s 8 MB main thread at about 6,000 recorded steps. A history
/// far longer than any budgeted proof records is dropped here on a 256 KB
/// thread, and dropped twice more with a shared suffix, since a node another
/// version still holds must stop the walk rather than be unlinked from under
/// it.
#[test]
fn recorded_snapshot_history_drops_without_recursing() {
    let build = |size: usize| {
        let mut snapshots = RecordedSnapshots::new();
        for index in 0..size {
            snapshots.insert(
                SnapshotSelector::Mark(format!("step-{index:06}")),
                CState::new(),
            );
        }
        snapshots
    };
    std::thread::Builder::new()
        .name("recorded-snapshot-history-drop".into())
        .stack_size(256 * 1024)
        .spawn(move || {
            drop(build(200_000));
            let shared = build(100_000);
            let mut longer = shared.clone();
            longer.insert(SnapshotSelector::Mark("tip".to_string()), CState::new());
            drop(longer);
            assert!(shared.contains_key(&SnapshotSelector::Mark("step-000000".to_string())));
            drop(shared);
        })
        .expect("thread")
        .join()
        .expect("dropping a recorded snapshot history must not recurse per node");
}

#[test]
fn recorded_snapshot_branch_merge_visits_only_fork_local_changes() {
    let mark_selector = |name: String| SnapshotSelector::Mark(name);
    let common_selector = mark_selector("common".to_string());
    let left_only = mark_selector("left-only".to_string());
    let right_only = mark_selector("right-only".to_string());
    let common_state = CState::new();
    let mut samples = Vec::new();

    for size in [16_usize, 64, 256, 1024, 4096] {
        let mut ancestor = RecordedSnapshots::new();
        for index in 0..size {
            ancestor.insert(mark_selector(format!("ambient-{index:05}")), CState::new());
        }
        let mut left = ancestor.clone();
        let mut right = ancestor.clone();
        left.insert(common_selector.clone(), common_state.clone());
        right.insert(common_selector.clone(), common_state.clone());
        left.insert(left_only.clone(), CState::new());
        right.insert(right_only.clone(), CState::new());

        let before = recorded_snapshot_node_allocations();
        let merged = left
            .common_descendant(&right, &ancestor)
            .expect("fork siblings should have an exact persistent ancestor");
        let allocations = recorded_snapshot_node_allocations() - before;
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
            Some(&CState::new())
        );
        assert_eq!(ancestor.iter().count(), size);

        let unrelated = RecordedSnapshots::new();
        assert!(left.common_descendant(&right, &unrelated).is_none());
    }

    let (_, base_height, base_allocations) = samples[0];
    for (size, height, allocations) in samples {
        let bound = base_allocations + 8 * (height - base_height);
        assert!(
            allocations <= bound,
            "size {size} recorded-snapshot merge allocated {allocations} nodes (logarithmic bound {bound})"
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
         \x20       initialize by simp;\n\
         \x20       preserve by {\n\
         \x20           have 0 <= n - 1 by {\n\
         \x20               apply(int32_positive_predecessor_is_nonnegative(n)) using { n > 0; }\n\
         \x20           }\n\
         \x20           step();\n\
         \x20           close_invariants by {\n\
         \x20               both { arithmetic() using { 0 <= n; } }\n\
         \x20               and {\n\
         \x20                   both { arithmetic() using { 0 <= n; } }\n\
         \x20                   and { arithmetic() using { 0 <= n; } }\n\
         \x20               }\n\
         \x20           }\n\
         \x20       }\n\
         \x20   }\n\
         \x20   step();\n\
         \x20   simp();\n\
         }\n",
    );
    (c_source, click_source)
}

#[test]
fn ranked_loop_bundle_scales_near_linearly_with_unrelated_inequalities() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = ranked_loop_with_unrelated_inequalities(size);
            let sources = [("ranked_drain.c", c_source.as_str())];
            let (verified, sample) =
                scaling_sample(size, || verify_c0_sources(&click_source, &sources));
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} ranked-loop scaling fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("ranked loop bundle with unrelated inequalities", &samples);
}

/// The same ranked loop closed by the smart `close_invariants()` planner.
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
         \x20       initialize by simp;\n\
         \x20       preserve by {\n\
         \x20           have 0 <= n - 1 by {\n\
         \x20               apply(int32_positive_predecessor_is_nonnegative(n)) using { n > 0; }\n\
         \x20           }\n\
         \x20           step();\n\
         \x20           close_invariants();\n\
         \x20       }\n\
         \x20   }\n\
         \x20   step();\n\
         \x20   simp();\n\
         }\n",
    );
    (c_source, click_source)
}

#[test]
fn smart_ranked_loop_bundle_scales_near_linearly_with_unrelated_inequalities() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = smart_ranked_loop_with_unrelated_inequalities(size);
            let sources = [("ranked_drain.c", c_source.as_str())];
            let (verified, sample) =
                scaling_sample(size, || verify_c0_sources(&click_source, &sources));
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
        .map(|k| format!("            have i <= n or {k} + i == 0 by {{ left(); }}\n"))
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
         \x20       initialize by simp;\n\
         \x20       preserve by {{\n\
         \x20           mark iteration;\n\
         \x20           have 0 <= at(iteration, i) by {{ simp(); }}\n\
         \x20           step();\n\
         \x20           have 0 <= i by {{ simp(); }}\n\
         \x20           have i <= n by {{ simp(); }}\n\
         \x20           have 0 <= i and i <= n by {{ split(); }}\n\
         {facts}\
         \x20           have 0 <= n - at(iteration, i) - 1 by {{\n\
         \x20               arithmetic() using {{\n\
         \x20                   0 <= at(iteration, i);\n\
         \x20                   at(iteration, i) < at(iteration, n);\n\
         \x20                   0 <= n;\n\
         \x20               }}\n\
         \x20           }}\n\
         \x20           have n - at(iteration, i) - 1 < n - at(iteration, i) by {{\n\
         \x20               arithmetic() using {{\n\
         \x20                   0 <= at(iteration, i);\n\
         \x20                   at(iteration, i) < at(iteration, n);\n\
         \x20                   0 <= n;\n\
         \x20               }}\n\
         \x20           }}\n\
         \x20           close_invariants();\n\
         \x20       }}\n\
         \x20   }}\n\
         \x20   step();\n\
         \x20   simp();\n\
         }}\n"
    );
    (c_source, click_source)
}

/// `close_invariants()` closes a bundle whose conjuncts sit under guards with
/// the direct logical steps alone, so its work follows the bundle's size.
/// Before, the closer ran the premise-selecting and rewriting strategies over
/// the whole bundle and every suffix of it first, and four guarded members
/// already exhausted the smart budget.
#[test]
fn smart_guarded_member_bundle_scales_near_linearly_with_conjuncts() {
    let samples = [2, 4, 8, 16]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = guarded_member_bundle(size);
            let sources = [("guarded_bundle.c", c_source.as_str())];
            let (verified, sample) =
                scaling_sample(size, || verify_c0_sources(&click_source, &sources));
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
                .get("smart tactic `close_invariants`")
                .copied()
                .unwrap_or(0),
            named_work: BTreeMap::new(),
        })
        .collect::<Vec<_>>();
    assert!(closer.iter().all(|sample| sample.work > 0), "{closer:?}");
    assert_near_linear_scaling("smart close_invariants over guarded members", &closer);
    // Far below the smart budget of 2,000,000 units, which four members
    // alone exhausted before the closer tried its direct steps first.
    assert!(closer.last().unwrap().work < 20_000, "{closer:?}");
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
fn call_requirement_checking_scales_near_linearly_with_unrelated_caller_facts() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = call_with_structured_precondition(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(
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

    assert_near_linear_scaling(
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
fn explicit_simple_tactics_scale_with_source_while_ambient_facts_grow() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = explicit_simple_project_with_ambient_facts(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(&click_source, &[("straight.c", c_source.as_str())])
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
fn wide_execution_match_join_has_near_linear_width_work() {
    let mut samples = Vec::new();
    let mut certificate_sizes = Vec::new();
    for width in [4, 8, 16, 32] {
        let (click_source, c_source) = wide_execution_match_project(width);
        let (verified, sample) = scaling_sample(width, || {
            verify_c0_sources(&click_source, &[("read.c", c_source.as_str())])
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
    assert_near_linear_scaling("wide execution match join", &samples);
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
                 \x20           execute();\n\
                 \x20           let c = fold(cell(p), {{ model: Wide::V{index} }}, {{}});\n\
                 \x20           have wide_code(old(c.model)) == {index} by {{\n\
                 \x20               rewrite(old(c.model) == Wide::V{index});\n\
                 \x20               unfold(wide_code(Wide::V{index}));\n\
                 \x20               normalize();\n\
                 \x20           }}\n\
                 \x20           simp();\n\
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
fn outcome_haves_and_resource_folds_do_not_reimport_ambient_facts() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let mut samples = Vec::new();
    for size in [8_usize, 16, 32, 64] {
        let requirements = (0..size)
            .map(|i| format!("requires x != {i};"))
            .collect::<String>();
        let mut baseline = None;
        for operations in [0_usize, 1, 4, 16] {
            let body = (0..operations)
                .map(|i| {
                    format!(
                        "have {} == {} by {{ normalize(); }} unfold(marker(x)); fold(marker(x));",
                        1000 + i,
                        1000 + i,
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
                }} by {{ execute(); {body} simp(); }}
            "#
            );
            crate::kernel::proof::take_fact_entry_counts();
            verify_c0_sources(&source, &[("identity.c", c_source)]).unwrap_or_else(|error| {
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

    let mut click_source = String::from("verifying \"cleanup.c\";\n\n");
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
        click_source.push_str(&format!("    requires x != {};\n", 10_000 + index));
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
fn exceptional_cleanup_edges_scale_near_linearly_with_unrelated_context() {
    const CALL_WORK: &str = "operation `verification statement: call assign`";
    let mut samples = Vec::new();
    let mut cleanup_work = Vec::new();
    for size in [2, 4, 8, 16] {
        let (c_source, click_source) = exceptional_cleanup_chain_project(size, size, size);
        let (verified, sample) = scaling_sample(size, || {
            verify_c0_sources(&click_source, &[("cleanup.c", c_source.as_str())])
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
    assert_near_linear_scaling("exceptional cleanup edges", &samples);
    assert_near_linear_scaling(
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
    for unrelated in [4, 8, 16, 32] {
        let (c_source, click_source) = exceptional_cleanup_chain_project(8, unrelated, unrelated);
        let (verified, sample) = scaling_sample(8, || {
            verify_c0_sources(&click_source, &[("cleanup.c", c_source.as_str())])
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
fn array_fact_across_local_stores(statement_count: usize) -> (String, String) {
    let mut c_source = String::from("void bump(int32 a[], int32 n) {\n    int32 i;\n    i = 0;\n");
    for _ in 0..statement_count {
        c_source.push_str("    i = i + 1;\n");
    }
    c_source.push_str("}\n");

    let mut click_source = String::from(
        "verifying \"bump.c\";\n\nfunction icount(p: int32[], lo: int32, hi: int32) -> Integer {\n    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })\n}\n\nvoid bump(int32 a[], int32 n) {\n    requires 0 < n;\n    requires viewable(a[0..n]);\n    views a[0..n];\n} by {\n    step();\n    step();\n    have 0 <= 0 by { simp(); }\n    have icount(a, 0, 0) == 0 by {\n        unfold(icount(a, 0, 0)) using { 0 <= 0; }\n        normalize();\n    }\n",
    );
    // One use of the fact after every step: the walk is asked from a fresh
    // snapshot each time, which is the shape that goes quadratic when an
    // epoch walk cannot reuse the answer it computed one snapshot ago.
    for _ in 0..statement_count {
        click_source.push_str("    step();\n");
        click_source.push_str("    have icount(a, 0, 0) == 0 by { simp(); }\n");
    }
    click_source.push_str("    execute();\n    simp();\n}\n");
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
        "verifying \"bump.c\";\n\nfunction icount(p: int32[], lo: int32, hi: int32) -> Integer {\n    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })\n}\n\nvoid bump(int32 a[], int32 n) {\n    requires 0 < n;\n    requires viewable(a[0..n]);\n    views a[0..n];\n} by {\n    have 0 <= 0 by { simp(); }\n    have icount(a, 0, 0) == 0 by {\n        unfold(icount(a, 0, 0)) using { 0 <= 0; }\n        normalize();\n    }\n",
    );
    for _ in 0..statement_count {
        click_source.push_str("    step();\n");
        click_source.push_str("    have icount(a, 0, 0) == 0 by { simp(); }\n");
    }
    click_source.push_str("    execute();\n    simp();\n}\n");
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
        "verifying \"keep_h.c\";\n\nfunction icount(p: int32[], lo: int32, hi: int32) -> Integer {\n    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })\n}\n\nvoid touch_g() {\n    owns g[0..1];\n} by {\n    execute();\n    simp();\n}\n\nint32 keep_h() {\n    requires h[0] == 5;\n    owns g[0..1];\n    views h[0..1];\n    ensures result == 5;\n} by {\n    have 0 <= 0 by { simp(); }\n    have icount(h, 0, 0) == 0 by {\n        unfold(icount(h, 0, 0)) using { 0 <= 0; }\n        normalize();\n    }\n",
    );
    for _ in 0..statement_count {
        click_source.push_str("    step();\n");
        click_source.push_str("    have icount(h, 0, 0) == 0 by { simp(); }\n");
    }
    click_source.push_str("    execute();\n    simp();\n}\n");
    (c_source, click_source)
}

/// The block epoch walk's own work over one fixture family, for the sizes
/// given. A missing entry means the fixture stopped exercising the walk, which
/// would make an assertion about its shape vacuous.
fn block_epoch_walk_curve(
    label: &str,
    file: &str,
    fixture: impl Fn(usize) -> (String, String),
) -> Vec<ScalingSample> {
    const WALK: &str = "operation `array-ref block epoch walk`";
    [4, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = fixture(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(&click_source, &[(file, c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!("size {size} {label} fixture failed: {}", error.message())
            });
            ScalingSample {
                size: sample.size,
                work: *sample
                    .named_work
                    .get(WALK)
                    .unwrap_or_else(|| panic!("fixture did not reach the epoch walk: {sample:?}")),
                named_work: BTreeMap::new(),
            }
        })
        .collect()
}

/// The two steps a whole-array fact learned to cross scale like the store it
/// always crossed: linear in the number of steps, not quadratic.
///
/// A declaration and a call are the interesting shapes because the walk crosses
/// them with different evidence -- one object proven distinct for a
/// declaration, a whole checked write set for a call -- and because a call's
/// arrival at a fresh snapshot per step is exactly the shape that goes
/// quadratic when the epoch walk cannot reuse the answer it computed one
/// snapshot ago.
#[test]
fn an_array_fact_carried_across_declarations_and_calls_scales_linearly() {
    assert_near_linear_scaling(
        "array-ref block epoch walk across declarations",
        &block_epoch_walk_curve("array-fact-across-declarations", "bump.c", |size| {
            array_fact_across_declarations(size)
        }),
    );
    assert_near_linear_scaling(
        "array-ref block epoch walk across calls",
        &block_epoch_walk_curve("array-fact-across-calls", "keep_h.c", |size| {
            array_fact_across_calls(size)
        }),
    );
}

/// Carrying one array fact across N steps that cannot touch the array costs
/// work linear in N, not quadratic.
///
/// The array argument names a block epoch, and the epoch is a walk back along
/// the derivation edges to the last one that could have changed the block. Run
/// per step with no memo, that walk is N hops at the Nth step and the proof
/// costs N^2; memoized per interned snapshot and block it is one hop per new
/// snapshot. This is the regression that tells those two apart.
#[test]
fn an_array_fact_carried_across_local_stores_scales_linearly() {
    let samples = [4, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = array_fact_across_local_stores(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(&click_source, &[("bump.c", c_source.as_str())])
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

    // The walk itself is the part at risk, and it is a small share of a
    // proof's work, so assert on its own measured work rather than on the
    // total it hides inside. A missing entry means the fixture stopped
    // exercising the walk at all, which would make the rest vacuous.
    const WALK: &str = "operation `array-ref block epoch walk`";
    let walk = samples
        .iter()
        .map(|sample| ScalingSample {
            size: sample.size,
            work: *sample
                .named_work
                .get(WALK)
                .unwrap_or_else(|| panic!("fixture did not reach the epoch walk: {sample:?}")),
            named_work: BTreeMap::new(),
        })
        .collect::<Vec<_>>();
    assert_near_linear_scaling("array-ref block epoch walk", &walk);
}

/// One project with `size` stores made while `size` owned ranges are held, so
/// that every store's per-cell drop is asked about a composition with `size`
/// members.
///
/// This is the shape that pays for
/// `memory_provenance::owned_composition_store_separated_evidence`: it runs
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
        "resource MaybeRaw(p: int32*) {\n    if p != 0 {\n        owns p[0..1];\n    }\n}\nresource Cell(p: int32*) {\n    owns p[0..1];\n}\nresource MaybeCell(p: int32*) {\n    if p != 0 { owns Cell(p); }\n}\ncontract int32* Raw() {\n    produces MaybeRaw(result);\n}\ncontract int32* Boxed() {\n    produces MaybeCell(result);\n}\ntheorem lift(acquire: int32* (*)()) executes acquire() {\n    requires Raw(acquire);\n    ensures Boxed(acquire) by {\n        step(Raw);\n        if result != 0 {\n            unfold(MaybeRaw(result));\n            fold(Cell(result));\n            fold(MaybeCell(result));\n            simp();\n        } else {\n            unfold(MaybeRaw(result));\n            fold(MaybeCell(result));\n            simp();\n        }\n    }\n}\nverifying \"acquire.c\";\nint32* read_acquired(int32* (*acquire)(), int32* value) {\n    requires Raw(acquire);\n",
    );
    click_source.push_str(&format!("    owns value[0..{size}];\n"));
    // One claim, not one per store: the fixture is here to measure the
    // per-store composition query, and `size` claims about `size` stores
    // would be quadratic before the query is ever reached.
    click_source.push_str(
        "    produces MaybeCell(result);\n    ensures result != 0 implies value[0] == result[0];\n} by {\n    apply(lift(acquire));\n    step();\n    step(Boxed);\n    if c(cell) != 0 {\n        unfold(MaybeCell(c(cell)));\n        unfold(Cell(c(cell)));\n        execute();\n        fold(Cell(result));\n        fold(MaybeCell(result));\n        simp();\n    } else {\n        unfold(MaybeCell(c(cell)));\n        execute();\n        fold(MaybeCell(result));\n        simp();\n    }\n}\n",
    );
    (c_source, click_source)
}

/// The cost contract for the composition disjunct on the store path
/// (`docs/internals/verification-efficiency.md`): stores and held owned
/// ranges grow together, and the work must not turn over into their product.
#[test]
fn stores_beside_many_owned_ranges_scale_near_linearly() {
    let samples = [2, 4, 8, 16]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = stores_beside_many_owned_ranges(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(&click_source, &[("acquire.c", c_source.as_str())])
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

    // And on the query's own measured work, so a regression in it cannot hide
    // inside the proof's total. A missing entry would mean the fixture stopped
    // reaching the query, which would make the assertion above vacuous.
    const QUERY: &str = "operation `composition-owned store separation`";
    let query = samples
        .iter()
        .map(|sample| ScalingSample {
            size: sample.size,
            work: *sample.named_work.get(QUERY).unwrap_or_else(|| {
                panic!("fixture did not reach the composition query: {sample:?}")
            }),
            named_work: BTreeMap::new(),
        })
        .collect::<Vec<_>>();
    assert_near_linear_scaling("composition-owned store separation", &query);
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

const ROUNDTRIP_CLICK: &str = "verifying \"rep_copy.c\";\n\nint f() {\n    ensures result == 18 or result == -1;\n} by {\n    execute();\n    simp();\n}\n";

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
        verify_c0_sources(ROUNDTRIP_CLICK, &[("rep_copy.c", c.as_str())])
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
/// the grouped proof's shared execution once per path theorem. Before snapshot
/// sharing they were about 33,000 at N = 8 and 58,000 at N = 16: every later
/// free compared the copy's facts, whose embedded snapshots were equal but
/// separately stored, entry by entry. Before resource validity read only
/// indexed candidates they were 3236, 3288, 3364, and 3548: each call's
/// ensured-resource composition swept every block the caller owned.
///
/// This guards those collapses; it is not the logarithmic contract, which
/// the expanded proof meets (see the next test). The remaining growth, about
/// 17 units per unrelated allocation, is mostly the
/// smart `execute` planner's condition-premise search over its listed pure
/// facts and that search's simp checkpoints (about 12 per allocation); the
/// rest is re-derived snapshot comparison relative to a base and more
/// composition separation-candidate projections. The kernel call path is
/// flat here: `ensured resource composition` and `verified call return
/// resource evaluation` charge the same work at every size.
#[test]
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

/// Expands the round trip's `execute(); simp();` proof beside `unrelated`
/// allocations to explicit simple tactics, outside the measurement, and
/// returns the C source length with the expanded proof's verification work.
fn expanded_roundtrip_sample(unrelated: usize, extra_copies: usize) -> (usize, ScalingSample) {
    std::thread::Builder::new()
        .name(format!("expanded-roundtrip-{unrelated}-{extra_copies}"))
        .stack_size(64 << 20)
        .spawn(move || {
            let c = roundtrip_with_unrelated_allocations(unrelated, extra_copies);
            let sources = [("rep_copy.c", c.as_str())];
            let expanded =
                expand_c0_claim_source(ROUNDTRIP_CLICK, &sources, "f", CProofClaim::Grouped)
                    .unwrap_or_else(|error| {
                        panic!(
                            "round trip beside {unrelated} allocations with {extra_copies} extra copies should expand: {}",
                            error.message()
                        )
                    });
            assert!(!expanded.contains("execute()"), "{expanded}");
            assert!(!expanded.contains("simp()"), "{expanded}");
            let (verified, sample) =
                scaling_sample(unrelated, || verify_c0_sources(&expanded, &sources));
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
///
/// This is the contract the smart test above does not meet: both variants'
/// `execute(); simp();` proofs are expanded outside the measurement, and only
/// the two expanded proofs' verification is compared. Seven allocations is
/// the largest family member the checked proof drivers' nesting bound admits
/// (see [`EXPANDED_ROUNDTRIP_MAX_UNRELATED`]). Measured marginals on
/// 2026-09-23 for 1 through 7 allocations: 912, 912, 912, 912, 916, 920, and
/// 920 units. The only growth is two `CMemory::eq_relative_to` comparisons
/// at each path's end (`proof completion`, re-deriving the memory without
/// the function's local block), whose persistent-map walk deepens with the
/// heap. Before finalization visited a grouped proof's shared execution once,
/// the marginals were 917, 918, 919, 920, 925, 930, and 931, one more unit
/// per allocation: the extra copy's composition carrier was re-inserted into
/// a fresh fact context once per theorem, and a grouped proof issues one
/// theorem per path.
#[test]
fn expanded_roundtrip_extra_copy_is_logarithmic_beside_unrelated_allocations() {
    const SIZES: [usize; 4] = [1, 2, 4, EXPANDED_ROUNDTRIP_MAX_UNRELATED];
    let marginal = expanded_roundtrip_samples(&SIZES)
        .iter()
        .map(|[(_, without), (_, with)]| with.work as i64 - without.work as i64)
        .collect::<Vec<_>>();
    eprintln!("expanded extra-copy marginal work beside {SIZES:?} allocations: {marginal:?}");
    assert!(marginal[0] > 0, "{marginal:?}");
    for (size, work) in SIZES.iter().zip(&marginal) {
        // Four units per doubling of the unrelated allocations; the measured
        // curve rises eight units by seven allocations, and a single unit
        // per allocation would exceed this by seven.
        let allowed = marginal[0] as f64 + 4.0 * (*size as f64 / SIZES[0] as f64).log2();
        assert!(
            *work as f64 <= allowed,
            "one extra memcpy under the expanded proof grew beyond {allowed} beside {size} allocations: {marginal:?}"
        );
    }
}

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
fn expanded_roundtrip_work_per_source_byte_is_logarithmic() {
    const SIZES: [usize; 4] = [1, 2, 4, EXPANDED_ROUNDTRIP_MAX_UNRELATED];
    let samples = expanded_roundtrip_samples(&SIZES);
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

/// Whole-function finalization reads each path of a grouped proof's checked
/// execution once, however many paths the proof issues theorems for.
///
/// A grouped proof issues one theorem per path and claim, all over one
/// shared execution. The implicit empty-effect check used to walk every path
/// of that execution once per theorem, rebuilding each path's fact context
/// each time, so its work was quadratic in the path count. Measured
/// `implicit empty effect check` work on 2026-09-23 at 4, 8, 16, and 32 early
/// returns: 5, 9, 17, and 33 units, one per composition carrier inserted into
/// a path's fact context. Visiting the execution once per theorem measured
/// 30, 90, 306, and 1122.
#[test]
fn grouped_proof_finalization_reads_each_path_once() {
    std::thread::Builder::new()
        .name("grouped-finalization-fan-out".into())
        .stack_size(64 << 20)
        .spawn(|| {
            let _ = roundtrip_sample(1, 0);
            const CHECK: &str = "operation `implicit empty effect check`";
            let click = "verifying \"fan_out.c\";\n\nint g(int a) {\n    ensures result == a or result == -1;\n} by {\n    execute();\n    simp();\n}\n";
            let samples = [4, 8, 16, 32]
                .map(|returns| {
                    let c = early_return_fan_out(returns);
                    let (verified, sample) = scaling_sample(returns, || {
                        verify_c0_sources(click, &[("fan_out.c", c.as_str())])
                    });
                    verified.unwrap_or_else(|error| {
                        panic!("fan-out of {returns} returns failed: {}", error.message())
                    });
                    ScalingSample {
                        size: returns,
                        work: *sample.named_work.get(CHECK).unwrap_or_else(|| {
                            panic!("fan-out did not reach the implicit empty-effect check: {sample:?}")
                        }),
                        named_work: BTreeMap::new(),
                    }
                })
                .to_vec();
            eprintln!("implicit empty-effect check work: {samples:?}");
            assert_near_linear_scaling("implicit empty-effect check over paths", &samples);
        })
        .expect("spawn the fan-out thread")
        .join()
        .expect("fan-out thread");
}

/// A fixed one-store proof verified after an unrelated proof in the same
/// sidecar. Everything a proof unit builds in the session (interned snapshots,
/// load names, memo tables) outlives it, so this is where a later proof can
/// end up walking an earlier one's history. The naming cache once returned
/// load names minted by the earlier function without refreshing their origin,
/// and the later store's pointer transport walked the earlier function's DAG
/// from that origin: 30,000 units alone became over a million, and the
/// arena's `arena_write` failed its budget only when `arena_init` ran first.
#[test]
fn a_fixed_store_proof_costs_the_same_after_a_growing_unrelated_proof() {
    const RESOURCES: &str = "resource box_state(b: struct box*) {
    field len: int32;
    owns &b->data;
    owns b->len;
    owns b->data[0..len];
    fact b->len == len;
    fact 0 <= len;
    fact separate(memory(object(b)), memory(b->data[0..b->len]));
}

resource holder_state(h: struct holder*) {
    field start: int32;
    owns object(h);
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
        simp() using {
            defined(s + i) and s + i < l;
        }
    }
    have s + i < l by {
        simp() using {
            defined(s + i) and s + i < l;
        }
    }
    have s <= s + i by {
        apply(int32_add_nonnegative_right_is_at_least_left(s, i)) using {
            0 <= i;
            defined(s + i);
        }
    }
    have s + i + 1 <= l by {
        apply(int32_increment_upper_bound(s + i, l)) using {
            s + i < l;
        }
    }
    have h->start == s by {
        assumption();
    }
    have defined(h->start + i) by {
        rewrite(h->start == s);
        assumption();
    }
    have h->start <= h->start + i by {
        rewrite(h->start == s);
        assumption();
    }
    have h->start + i + 1 <= l by {
        rewrite(h->start == s);
        assumption();
    }
    execute();
    let r = fold(holder_state(h), { start: s });
    let st = fold(box_state(h->box), { len: l });
    simp();
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
    execute();
    let st = fold(box_state(b), {{ len: l }});
    simp();
}}

"
                ),
            ),
        };
        let c_source = format!("{STRUCTS}\n{big_c}{FIXED_C}");
        let click_source =
            format!("{RESOURCES}\nverifying \"order.c\";\n\n{big_proof}{FIXED_PROOF}");
        let (result, events) = crate::instrumentation::collect(|| {
            verify_c0_sources(&click_source, &[("order.c", &c_source)])
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
    let samples = [4, 8, 16, 32].map(|stores| (stores, fixed_proof_work(Some(stores))));
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
/// The explicit back-edge closure cites each cell's frame fact after
/// introducing the preceding written invariant clauses. Logical reads do
/// not add viewability goals or introductions to that certificate.
fn framed_field_cells_loop(cells: usize) -> (String, String) {
    let c_source = "struct arena {\n    int32* data;\n    int32* occupied;\n    int32 capacity;\n};\n\n\
        void mark_tail(struct arena* arena, int32 start, int32 end) {\n    int32 i;\n    i = start;\n    \
        while (i < end) {\n        arena->occupied[i] = 1;\n        i = i + 1;\n    }\n}\n"
        .to_string();
    let ranking = "arithmetic() using { 0 <= at(statement(3).entry, i); \
        at(statement(3).entry, i) < at(statement(3).entry, end); end <= 1000000; }";
    let mut members = vec!["simp();".to_string()];
    for cell in 0..cells {
        members.push(format!(
            "{}arithmetic_certificate signed_int32 {{ premise 0: arena->occupied[{cell}] == \
             old(arena->occupied[{cell}]) => arena->occupied[{cell}] == \
             old(arena->occupied[{cell}]); conclusion 0; }}",
            "intro(); ".repeat(1 + cell)
        ));
    }
    members.push(ranking.to_string());
    members.push(ranking.to_string());
    let closure = members
        .iter()
        .rev()
        .skip(1)
        .fold(members.last().unwrap().clone(), |rest, member| {
            format!("both {{ {member} }} and {{ {rest} }}")
        });
    let invariants = (0..cells)
        .map(|cell| {
            format!("        invariant arena->occupied[{cell}] == old(arena->occupied[{cell}]);\n")
        })
        .collect::<String>();
    let click_source = format!(
        "verifying \"mark_tail.c\";\n\n\
         void mark_tail(struct arena* arena, int32 start, int32 end) {{\n\
         \x20   owns object(arena);\n\
         \x20   owns arena->occupied[0..arena->capacity];\n\
         \x20   requires separate(\n\
         \x20       memory(object(arena)),\n\
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
         \x20       initialize by simp;\n\
         \x20       preserve by {{\n\
         \x20           have 0 <= i by {{ simp(); }}\n\
         \x20           step();\n\
         \x20           step();\n\
         \x20           close_invariants by {{ {closure} }}\n\
         \x20       }}\n\
         \x20   }}\n\
         \x20   execute();\n\
         \x20   simp();\n\
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
fn framed_field_cells_back_edge_closure_follows_its_certificate() {
    let samples = [1, 2, 4, 8]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = framed_field_cells_loop(size);
            let sources = [("mark_tail.c", c_source.as_str())];
            let (verified, sample) =
                scaling_sample(size, || verify_c0_sources(&click_source, &sources));
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
/// bound, closed by the smart `close_invariants()`.
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
         \x20       initialize by simp;\n\
         \x20       preserve by {{\n\
         \x20           step();\n\
         \x20           close_invariants();\n\
         \x20       }}\n\
         \x20   }}\n\
         \x20   execute();\n\
         \x20   simp();\n\
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
fn many_clause_bundle_grows_at_most_quadratically() {
    let samples = [2, 4, 8, 16]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = many_clause_loop(size);
            let sources = [("count.c", c_source.as_str())];
            let (verified, sample) =
                scaling_sample(size, || verify_c0_sources(&click_source, &sources));
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

/// `simp` closes `x0 == xN` from the chain `x0 == x1`, ..., `x(N-1) == xN`
/// in one step, with work linear in the chain; a query about two unrelated
/// equal terms costs the same whatever chain sits beside it.
#[test]
fn simp_equality_chain_is_linear_and_unrelated_queries_are_flat() {
    let simp_work = |sample: &ScalingSample| {
        sample
            .named_work
            .iter()
            .filter(|(name, _)| name.ends_with("tactic `simp`"))
            .map(|(_, work)| *work)
            .sum::<usize>()
    };
    let sources = |size: usize, goal: &str| {
        let c_parameters = (0..=size)
            .map(|index| format!("int x{index}"))
            .chain(["int y".into(), "int z".into(), "int w".into()])
            .collect::<Vec<_>>()
            .join(", ");
        let parameters = (0..=size)
            .map(|index| format!("int32 x{index}"))
            .chain(["int32 y".into(), "int32 z".into(), "int32 w".into()])
            .collect::<Vec<_>>()
            .join(", ");
        let requires = (0..size)
            .map(|index| format!("    requires x{index} == x{};\n", index + 1))
            .collect::<String>();
        (
            format!("int chain({c_parameters}) {{\n    return 0;\n}}\n"),
            format!(
                "verifying \"chain.c\";\n\nint32 chain({parameters}) {{\n{requires}    requires y == z;\n    requires z == w;\n    ensures {goal};\n}} by {{\n    execute();\n    simp();\n}}\n"
            ),
        )
    };
    let mut chain = Vec::new();
    let mut unrelated = Vec::new();
    for size in [4, 8, 16, 32] {
        for (goal, samples) in [
            (format!("x0 == x{size}"), &mut chain),
            ("y == w".to_string(), &mut unrelated),
        ] {
            let (c_source, click_source) = sources(size, &goal);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(&click_source, &[("chain.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| panic!("`{goal}` closes: {}", error.message()));
            samples.push(simp_work(&sample));
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
fn failing_simp_derivation_ignores_unrelated_disjunctions() {
    use crate::kernel::{Bitvector32Term, ConditionTerm, Proposition, PureFactContext, Variable};
    use crate::surface::planning::proposition_search::PropositionSearch;

    let equal = |variable: u64, value: u32| {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(Variable(variable))),
                Box::new(Bitvector32Term::Constant(value)),
            ),
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
            let goal = Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(
                    Box::new(Bitvector32Term::Variable(Variable(433_000))),
                    Box::new(Bitvector32Term::Constant(5)),
                ),
                true,
            );
            let (derivation, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.derive_simp_proposition(&goal)
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
        "} by {\n    step();\n    branch {\n        then {\n            execute();\n            simp();\n        }\n        else {}\n    }\n    step();\n    have x == a by {\n        simp();\n    }\n    execute();\n    simp();\n}\n",
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
fn grouped_proof_theorems_share_one_proof_text() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = branching_grouped_claim_project(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(&click_source, &[("branching_claims.c", c_source.as_str())])
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
            for theorem in &verified {
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
/// snapshot, so the counter's constant after normalization runs through the
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
        "verifying \"drive.c\";\n\nvoid touch(struct range* r) {\n    owns object(r);\n    requires r->end < 1000000;\n    ensures r->end == old(r->end) + 1;\n    ensures r->start == old(r->start);\n} by {\n    execute();\n    simp();\n}\n\n",
    );
    click_source.push_str(&format!(
        "void drive(struct range* r) {{\n    owns object(r);\n    requires r->end == 0;\n    ensures r->end == {call_count};\n}} by {{\n"
    ));
    for _ in 0..call_count {
        click_source.push_str("    step();\n");
    }
    click_source.push_str("    execute();\n    simp();\n}\n");
    (c_source, click_source)
}

/// A simple `step()` over a call lowers the callee's equality ensures in work
/// proportional to that call, not to the caller's prior call chain.
///
/// Normalizing an ensured term to its constant used to re-walk every earlier
/// call's ensures, deep-comparing each same-address load at another snapshot:
/// the Nth call cost O(N^2) and the proof O(N^3). The constant is now a class
/// lookup maintained as each fact is inserted, so the last call's lowering is
/// flat in N and the whole proof is near-linear.
#[test]
fn counter_call_chain_ensure_lowering_stays_flat_per_call() {
    const LOWERING: &str = "verified call provisional ensure lowering";
    let mut last_lowering = Vec::new();
    let mut totals = Vec::new();
    for size in [8, 16, 32, 64] {
        let (c_source, click_source) = counter_call_chain(size);
        let ((verified, work), events) = crate::instrumentation::collect(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&click_source, &[("drive.c", c_source.as_str())])
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
    assert_near_linear_scaling("counter call chain", &totals);
}

/// A copy loop whose preservation `simp` reaches a fact transport the
/// explicit-premise planner cannot view: the element just stored is named
/// `dst[k]` under `k == i - 1`, so `old(src[k]) == old(src[k])` does not
/// transport to it until `k` is rewritten. Each unrelated `requires` joins
/// the planner's candidate list. The planner decides the complete list
/// before it grows a prefix, so the failing plan costs the same number of
/// checks (six) at every size. It used to check once per growing prefix,
/// about 15k units per unrelated fact in each preservation attempt; the
/// remaining linear cost of lowering and offering a candidate is about 1k.
fn copy_loop_with_unrelated_requirements(fact_count: usize) -> String {
    let unrelated = (0..fact_count)
        .map(|index| format!("    requires length != {};\n", index + 100_000))
        .collect::<String>();
    format!(
        "verifying \"transport_copy.c\";\n\
         \n\
         int32 transport_copy(int32 dst[], int32 src[], int32 length) {{\n    \
             requires 0 <= length;\n    \
             requires ((uint32)length) <= 1073741823u32;\n    \
             owns dst[0..length];\n    \
             views src[0..length];\n    \
             requires separate(memory(dst[0..length]), memory(src[0..length]));\n\
         {unrelated}    \
             ensures result == length;\n\
         }} by {{\n    \
             step();\n    \
             step();\n    \
             loop {{\n        \
                 decreases length - i;\n        \
                 invariant 0 <= i;\n        \
                 invariant i <= length;\n        \
                 invariant forall (k: int32) {{ 0 <= k and k < i implies dst[k] == old(src[k]) }};\n        \
                 owns dst[0..length];\n        \
                 initialize by {{\n            \
                     have 0 <= i by {{\n                normalize();\n            }}\n            \
                     have i <= length by {{\n                assumption();\n            }}\n            \
                     have forall (k: int32) {{ 0 <= k and k < i implies dst[k] == old(src[k]) }} by {{\n                \
                         intro();\n                \
                         intro();\n                \
                         extract(0 <= k);\n                \
                         extract(k < i);\n                \
                         have i == 0 by {{\n                    normalize();\n                }}\n                \
                         have not (0 <= k) by {{\n                    \
                             arithmetic() using {{\n                        k < i;\n                        i == 0;\n                    }}\n                \
                         }}\n                \
                         contradiction(0 <= k);\n            \
                     }}\n        \
                 }}\n        \
                 preserve by {{\n            step();\n            step();\n            simp();\n        }}\n    \
             }}\n    \
             have i == length by {{\n        \
                 apply(int32_le_and_not_lt_implies_eq(at(loop(0).exit, i), at(loop(0).exit, length))) using {{\n            \
                     at(loop(0).exit, i) <= at(loop(0).exit, length);\n            \
                     not at(loop(0).exit, i) < at(loop(0).exit, length);\n        \
                 }}\n        \
                 assumption();\n    \
             }}\n    \
             step();\n    \
             simp();\n\
         }}\n"
    )
}

#[test]
fn failing_fact_transport_plan_ignores_unrelated_candidates() {
    const COPY_SOURCE: &str = "int32 transport_copy(int32 dst[], int32 src[], int32 length) {\n    \
                               int32 i;\n    i = 0;\n    while (i < length) {\n        \
                               dst[i] = src[i];\n        i = i + 1;\n    }\n    return i;\n}\n";
    let mut samples = Vec::new();
    let mut plan_checks = Vec::new();
    let mut simp_work = Vec::new();
    for size in [6, 12, 24, 48] {
        let click_source = copy_loop_with_unrelated_requirements(size);
        let ((verified, work), events) = crate::instrumentation::collect(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&click_source, &[("transport_copy.c", COPY_SOURCE)])
            })
        });
        verified.unwrap_or_else(|error| {
            panic!(
                "size {size} fact-transport scaling fixture failed: {}",
                error.message()
            )
        });
        let mut named_work = BTreeMap::<String, usize>::new();
        let mut checks = 0;
        let mut simp = 0;
        for event in events {
            match event {
                crate::instrumentation::VerificationEvent::OperationFinished {
                    name, work, ..
                } => {
                    if name == "explicit fact transport: premise check" {
                        checks += 1;
                    }
                    *named_work.entry(format!("operation `{name}`")).or_default() += work;
                }
                crate::instrumentation::VerificationEvent::TacticFinished {
                    tactic, work, ..
                } => {
                    if tactic.tactic_name == "simp" {
                        simp += work;
                    }
                    *named_work
                        .entry(format!("{} tactic `{}`", tactic.class, tactic.tactic_name))
                        .or_default() += work;
                }
                _ => {}
            }
        }
        plan_checks.push(checks);
        simp_work.push(simp);
        samples.push(ScalingSample {
            size,
            work,
            named_work,
        });
    }
    assert!(
        plan_checks[0] > 0,
        "the preservation simp never planned a fact transport: {plan_checks:?}"
    );
    assert!(
        plan_checks.iter().all(|checks| *checks == plan_checks[0]),
        "fact-transport planning checked once per unrelated candidate: {plan_checks:?}; \
         named work: {}",
        named_growth_diagnostic(&samples)
    );
    // Each unrelated requirement is still read, lowered, and offered as a
    // candidate, which is linear; a check per candidate cost an order of
    // magnitude more per fact.
    let per_fact = (simp_work[3] - simp_work[0]) / (48 - 6);
    assert!(
        per_fact <= 4_000,
        "simp work grew by {per_fact} units per unrelated requirement: {simp_work:?}"
    );
    assert_near_linear_scaling("fact-transport plan unrelated candidates", &samples);
}
