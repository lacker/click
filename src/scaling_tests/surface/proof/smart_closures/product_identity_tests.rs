// Scaling coverage for the product identity `solve` plans
// (`prove_operation_identities`, `prove_product_bound_from_ranges`).

/// The product's lower bound comes from its operands' type ranges and its
/// identity from the two bounds, so the `solve` that plans them does no more
/// work as unrelated parameters and facts grow. One theorem per size, in one
/// source, so the library is set up once.
#[test]
fn product_identity_planning_ignores_unrelated_facts() {
    let sizes = [0usize, 8, 32];
    let source = sizes
        .iter()
        .map(|size| {
            let parameters = (0..*size)
                .map(|index| format!(", u{index}: uint16"))
                .collect::<String>();
            let unrelated = (0..*size)
                .map(|index| format!("    requires to_integer(u{index}) <= {index};\n"))
                .collect::<String>();
            format!(
                "theorem product_identity_{size}(a: uint16, b: uint16{parameters}) {{
{unrelated}    requires to_integer(a) * to_integer(b) <= 65535;
    let r: uint16 = a * b;
    ensures to_integer(r) == to_integer(a) * to_integer(b) by {{
        have to_integer(r) == to_integer(a) * to_integer(b) by close();
        close();
    }}
}}
"
            )
        })
        .collect::<String>();
    let (result, work) = crate::instrumentation::collect_tactic_work(|| {
        crate::surface::verify_click_theorems(&source)
    });
    result.unwrap();
    let samples = work
        .iter()
        .filter(|sample| sample.tactic.tactic_name == "close" && sample.tactic.class == "smart")
        .map(|sample| sample.work)
        .collect::<Vec<_>>();
    assert_eq!(samples.len(), sizes.len(), "{samples:?}");
    let baseline = samples[0];
    assert!(
        samples.iter().all(|work| *work <= baseline + 64),
        "unrelated facts grew the product identity's planning at sizes {sizes:?}: {samples:?}"
    );
}
