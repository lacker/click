// Scaling tests for scalar induction script preparation and checked prefixes.

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.67s focused scalar-induction prefixes at four sizes"]
fn scalar_induction_prefix_work_scales_with_explicit_helpers() {
    let template = "theorem prefix(n: int32) { requires n >= 0; ensures n >= 0 by { have n == n; let ih = induct(n); close(); } }";
    let samples = [8, 16, 32, 64].map(|size| {
        let source = template.replace("have n == n;", &"have n == n by close();\n".repeat(size));
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::surface::verify_c_sources(&source, &[])
        });
        result.unwrap();
        work
    });
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3,
            "induction prefix work must scale with the written script: {samples:?}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: structural induction scope scaling at four prefix sizes"]
fn structural_induction_prefix_work_scales_with_explicit_helpers() {
    let fixture =
        include_str!("../../../../../mdtests/structural_induction_surrounding_helpers.md");
    let source = fixture
        .split_once("```click\n")
        .unwrap()
        .1
        .split_once("\n```")
        .unwrap()
        .0;
    let samples = [8, 16, 32, 64].map(|size| {
        let helpers = "have n == n by close();\n".repeat(size);
        let source = source.replace(
            "have before: n >= 0 by close();",
            &format!("{helpers}have before: n >= 0 by close();"),
        );
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::surface::verify_c_sources(&source, &[])
        });
        result.unwrap();
        work
    });
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3,
            "structural prefix work scales with explicit helpers: {samples:?}"
        );
    }
}
