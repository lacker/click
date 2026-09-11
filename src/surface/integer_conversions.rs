//! Public spelling and source types of explicit Integer conversions.
use super::*;

pub(super) fn integer_conversion_target(name: &str) -> Option<C0Type> {
    Some(match name {
        "to_int16" => C0Type::Int16,
        "to_int32" => C0Type::Int32,
        "to_uint8" => C0Type::UInt8,
        "to_uint16" => C0Type::UInt16,
        "to_uint32" => C0Type::UInt32,
        "to_int64" => C0Type::Int64,
        "to_uint64" => C0Type::UInt64,
        _ => return None,
    })
}

pub(super) fn is_integer_conversion(name: &str) -> bool {
    name == "to_integer" || integer_conversion_target(name).is_some()
}

pub(super) fn machine_integer_source_type(c_type: C0Type) -> bool {
    matches!(
        c_type,
        C0Type::Int16
            | C0Type::Int32
            | C0Type::UInt8
            | C0Type::UInt16
            | C0Type::UInt32
            | C0Type::Int64
            | C0Type::UInt64
    )
}

pub(super) fn integer_conversion_argument<'a>(
    name: &str,
    arguments: &'a [ContractExpression],
) -> Result<&'a ContractExpression, String> {
    let [argument] = arguments else {
        return Err(format!(
            "conversion `{name}` expects one argument, got {}",
            arguments.len()
        ));
    };
    Ok(argument)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn integer_bounds_establish_c_add_definedness_without_circular_assumptions() {
        let source = "theorem safety(a: int32, b: int32) { requires to_integer(a) + to_integer(b) >= -2147483648; requires to_integer(a) + to_integer(b) <= 2147483647; ensures defined(a + b) by { apply(int32_add_defined_by_integer_bounds(a, b)); } }";
        verify_c0_sources(source, &[]).unwrap();
        let expanded = expand_c0_claim_source_by_label(source, &[], "safety.ensures_0").unwrap();
        verify_c0_sources(&expanded, &[]).unwrap();
        for missing in [
            "requires to_integer(a) + to_integer(b) >= -2147483648;",
            "requires to_integer(a) + to_integer(b) <= 2147483647;",
        ] {
            let invalid = source.replace(missing, "");
            assert!(verify_c0_sources(&invalid, &[]).is_err(), "{invalid}");
        }
    }

    #[test]
    fn integer_machine_operation_laws_require_definedness() {
        for (name, operator) in [
            ("int32_add_to_integer", "+"),
            ("int32_subtract_to_integer", "-"),
        ] {
            let source = format!(
                "theorem bridge(a: int32, b: int32) {{ requires defined(a {operator} b); ensures to_integer(a {operator} b) == to_integer(a) {operator} to_integer(b) by {{ apply({name}(a, b)); }} }}"
            );
            verify_c0_sources(&source, &[]).unwrap_or_else(|e| panic!("{}\n{source}", e.message()));
            let expanded =
                expand_c0_claim_source_by_label(&source, &[], "bridge.ensures_0").unwrap();
            verify_c0_sources(&expanded, &[]).unwrap();
            let invalid = source.replace(&format!("requires defined(a {operator} b);"), "");
            assert!(verify_c0_sources(&invalid, &[]).is_err(), "{invalid}");
        }
    }

    #[test]
    fn integer_conversion_aliases_preserve_shared_expression_scaling() {
        let mut measured = Vec::new();
        for depth in [8, 16, 32, 64] {
            let mut source =
                String::from("theorem aliases(x: int32) { let a0: Integer = to_integer(x);\n");
            for index in 1..=depth {
                source.push_str(&format!(
                    "let a{index}: Integer = a{} + a{};\n",
                    index - 1,
                    index - 1
                ));
            }
            source.push_str(&format!("requires a{depth} == a{depth}; ensures a{depth} == a{depth} by {{ assumption(); }} }}"));
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&source, &[])
            });
            result.unwrap_or_else(|error| panic!("depth {depth}: {}", error.message()));
            measured.push(work);
        }
        for pair in measured.windows(2) {
            assert!(
                pair[1] <= 3 * pair[0],
                "conversion aliases expanded their shared tree: {measured:?}"
            );
        }
    }

    #[test]
    fn integer_conversion_proofs_expand_and_recheck() {
        for source in [
            "theorem conversion(x: int32) { ensures to_integer(x) == to_integer(x) by simp; }",
            "theorem conversion() { ensures to_integer(to_uint64(18446744073709551615)) == 18446744073709551615 by simp; }",
        ] {
            verify_c0_sources(source, &[]).unwrap();
            let expanded =
                expand_c0_claim_source_by_label(source, &[], "conversion.ensures_0").unwrap();
            verify_c0_sources(&expanded, &[])
                .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
            assert!(!expanded.contains("by simp"), "{expanded}");
        }
    }

    #[test]
    fn integer_conversion_rejects_each_out_of_range_boundary() {
        for (target, lower, upper) in [
            ("int16", "-32769", "32768"),
            ("int32", "-2147483649", "2147483648"),
            ("uint8", "-1", "256"),
            ("uint16", "-1", "65536"),
            ("uint32", "-1", "4294967296"),
            ("int64", "-9223372036854775809", "9223372036854775808"),
            ("uint64", "-1", "18446744073709551616"),
        ] {
            for value in [lower, upper] {
                let source = format!(
                    "theorem bad() {{ ensures to_{target}({value}) == to_{target}({value}) by simp; }}"
                );
                assert!(
                    verify_c0_sources(&source, &[]).is_err(),
                    "out-of-range conversion accepted: {source}"
                );
            }
        }
    }

    #[test]
    fn integer_conversion_preserves_source_types_and_argument_definedness() {
        for (parameters, claim) in [
            ("", "to_integer(true) == 1"),
            ("", "to_integer() == 0"),
            ("", "to_integer(1, 2) == 1"),
            ("", "to_int32() == 0"),
            ("", "to_int32(1, 2) == 1"),
            ("x: int32", "to_integer(x) == x"),
            ("x: int32", "to_int32(x) == x"),
            ("z: Integer", "to_integer(z) == z"),
            ("", "to_integer(-1) == to_integer(4294967295u32)"),
            (
                "",
                "to_integer(2147483647 + 1) == to_integer(2147483647 + 1)",
            ),
        ] {
            let source = format!("theorem bad({parameters}) {{ ensures {claim} by simp; }}");
            assert!(
                verify_c0_sources(&source, &[]).is_err(),
                "invalid conversion accepted: {source}"
            );
        }
    }
}
