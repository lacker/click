//! Explicit, guarded mathematical truncation, separate from Integer `/` policy.
use super::*;

pub(in crate::surface) fn is_integer_truncation(name: &str) -> bool {
    matches!(name, "truncating_quotient" | "truncating_remainder")
}

pub(super) fn integer_truncation_arguments<'a>(
    name: &str,
    arguments: &'a [ContractExpression],
) -> Result<(&'a ContractExpression, &'a ContractExpression), String> {
    let [left, right] = arguments else {
        return Err(format!("{name} expects two Integer arguments"));
    };
    Ok((left, right))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn verify(source: &str) {
        verify_c_sources(source, &[]).unwrap_or_else(|e| panic!("{}\n{source}", e.message()));
    }

    #[test]
    fn integer_truncation_constants_and_full_width_signs_verify_and_expand() {
        for (term, expected) in [
            ("truncating_quotient(-7, 3)", "-2"),
            ("truncating_remainder(-7, 3)", "-1"),
            ("truncating_quotient(7, -3)", "-2"),
            ("truncating_remainder(7, -3)", "1"),
            (
                "truncating_quotient(-170141183460469231731687303715884105728, -1)",
                "170141183460469231731687303715884105728",
            ),
            (
                "truncating_remainder(340282366920938463463374607431768211455, 3)",
                "0",
            ),
        ] {
            let source =
                format!("theorem truncation() {{ ensures {term} == {expected} by close(); }}");
            verify(&source);
            let expanded =
                expand_c_claim_source_by_label(&source, &[], "truncation.ensures_0").unwrap();
            verify(&expanded);
            assert!(
                verify_c_sources(
                    &source.replace(&format!("== {expected}"), &format!("== ({expected}) + 1")),
                    &[]
                )
                .is_err()
            );
        }
    }

    #[test]
    fn integer_truncation_symbolic_domain_survives_proofs_and_expansion() {
        for function in ["truncating_quotient", "truncating_remainder"] {
            for expression in [
                format!("{function}(a, b)"),
                format!("0 * {function}(a, b)"),
                format!("{function}(a, b) * 0"),
                format!("{function}(a, b) - {function}(a, b)"),
            ] {
                let source = format!(
                    "theorem truncation(a: Integer, b: Integer) {{ requires b != 0; ensures {expression} == {expression} by close(); }}"
                );
                verify(&source);
                let expanded =
                    expand_c_claim_source_by_label(&source, &[], "truncation.ensures_0").unwrap();
                verify(&expanded);
                assert!(
                    verify_c_sources(&source.replace("requires b != 0;", ""), &[]).is_err(),
                    "{source}"
                );
            }
        }
    }

    #[test]
    fn integer_truncation_rejects_zero_wrong_types_arities_and_shadowing() {
        for expression in [
            "truncating_quotient(7, 0)",
            "truncating_remainder(7, 0)",
            "0 * truncating_quotient(7, 0)",
            "truncating_remainder(7, 0) * 0",
            "truncating_quotient()",
            "truncating_remainder(1)",
            "truncating_quotient(1, 2, 3)",
            "truncating_quotient(x, 3)",
            "truncating_remainder(true, 3)",
        ] {
            let source = format!(
                "theorem bad(x: int32) {{ ensures {expression} == {expression} by close(); }}"
            );
            assert!(verify_c_sources(&source, &[]).is_err(), "{source}");
        }
        for function in ["truncating_quotient", "truncating_remainder"] {
            let source = format!("function {function}(a: Integer, b: Integer) -> Integer {{ a }}");
            assert!(verify_c_sources(&source, &[]).is_err());
        }
    }

    #[test]
    fn integer_truncation_preserves_operand_native_definedness() {
        for function in ["truncating_quotient", "truncating_remainder"] {
            let expression = format!("{function}(to_integer(x + 1), 3)");
            let source = format!(
                "theorem truncation(x: int32) {{ requires defined(x + 1); ensures {expression} == {expression} by close(); }}"
            );
            verify(&source);
            let expanded =
                expand_c_claim_source_by_label(&source, &[], "truncation.ensures_0").unwrap();
            verify(&expanded);
            assert!(
                verify_c_sources(&source.replace("requires defined(x + 1);", ""), &[]).is_err()
            );
        }
    }
    #[test]
    fn integer_truncation_function_arguments_keep_their_domain() {
        for helper in ["truncating_quotient", "truncating_remainder"] {
            let expression = format!("identity({helper}(a, b))");
            let source = format!(
                "function identity(x: Integer) -> Integer {{ x }} theorem client(a: Integer, b: Integer) {{ requires b != 0; ensures {expression} == {expression} by close(); }}"
            );
            verify(&source);
            let expanded =
                expand_c_claim_source_by_label(&source, &[], "client.ensures_0").unwrap();
            verify(&expanded);
            assert!(verify_c_sources(&source.replace("requires b != 0;", ""), &[]).is_err());
        }
        let too_wide = "theorem bad() { ensures to_int128(truncating_quotient(-170141183460469231731687303715884105728, -1)) == to_int128(truncating_quotient(-170141183460469231731687303715884105728, -1)) by close(); }";
        assert!(verify_c_sources(too_wide, &[]).is_err());
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/surface/integer_truncation/tests.rs");
    }
}
