// Scaling tests of `src/surface/tests/tactic_tests/logical_tactics.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn pure_witness_integer_aliases_keep_shared_term_scaling() {
    for function_backed in [false, true] {
        let mut measured = Vec::new();
        for depth in [8, 16, 32, 64] {
            let mut source = if function_backed {
                "function f(x: Integer, y: Integer) -> Integer { x + y }\n theorem aliases(x: Integer) { let a0: Integer = x;\n".to_owned()
            } else {
                "theorem aliases(x: int32) { let a0: Integer = to_integer(x);\n".to_owned()
            };
            for index in 1..=depth {
                let previous = index - 1;
                let value = if function_backed {
                    format!("f(a{previous}, a{previous})")
                } else {
                    format!("a{previous} + a{previous}")
                };
                source.push_str(&format!("let a{index}: Integer = {value};\n"));
            }
            source.push_str(&format!("ensures exists (q: Integer) {{ q == a{depth} }} by {{ witness(a{depth}); close(); }} }}"));
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c_sources(&source, &[])
            });
            result.unwrap_or_else(|error| {
                panic!(
                    "function backed {function_backed}, depth {depth}: {}",
                    error.message()
                )
            });
            measured.push(work);
        }
        for pair in measured.windows(2) {
            assert!(
                pair[1] <= 3 * pair[0],
                "witness aliases must retain shared terms: {measured:?}"
            );
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: three cold call-history proofs"]
fn extracting_two_call_equalities_ignores_earlier_call_history() {
    let mut measured = Vec::new();
    for preceding in [2usize, 4, 8] {
        let c = format!(
            "void keep(int *v, int n, int to) {{}}\nvoid caller(int *v, int n, int to) {{ {} }}",
            "keep(v, n, to);".repeat(preceding + 2),
        );
        let source = format!(
            r#"
            verifying "extract.c";
            void keep(int32* v, int32 n, int32 to) {{
                requires 0 <= n;
                owns v[0..n];
                ensures 0 <= to and to < n implies v[to] == old(v[to]);
            }}
            void caller(int32* v, int32 n, int32 to) {{
                requires 0 <= n;
                owns v[0..n];
            }} by {{
                {}
                mark start;
                step();
                mark middle;
                step();
                have 0 <= to and to < n implies v[to] == at(start, v[to]) by {{
                    intro();
                    have v[to] == at(middle, v[to]) by close();
                    have at(middle, v[to]) == at(start, v[to]) by close();
                    close();
                }}
                step();
                close();
            }}
        "#,
            "step();".repeat(preceding)
        );
        let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
            verify_c_sources(&source, &[("extract.c", c.as_str())])
        });
        result.unwrap_or_else(|error| panic!("{preceding}: {}", error.report()));
        let work = samples
            .iter()
            .filter(|sample| {
                sample.tactic.claim == "caller.contract" && sample.tactic.tactic_name == "have"
            })
            .map(|sample| sample.work)
            .max()
            .expect("selected two-call equality proof");
        measured.push(work);
    }
    assert!(
        measured.windows(2).all(|pair| pair[1] <= pair[0] + 128),
        "fixed two-call proof must ignore earlier calls: {measured:?}"
    );
}
