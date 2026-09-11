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
    fn conversion_obligations_survive_right_operand_composition() {
        for expression in [
            "1 + to_integer(x + 1)",
            "to_integer(x + 1) + 1",
            "to_integer(x) + to_integer(x + 1)",
        ] {
            let source = format!(
                "theorem compose(x: int32) {{ ensures {expression} == {expression} by simp; }}"
            );
            assert!(verify_c0_sources(&source, &[]).is_err(), "{source}");
            let bounded = source.replace("{ ensures", "{ requires defined(x + 1); ensures");
            verify_c0_sources(&bounded, &[]).unwrap();
        }
    }

    #[test]
    fn forward_conversion_conditionals_preserve_the_argument_domain() {
        let expression = "if c == 0 { x + 1 } else { y + 1 }";
        let source = format!(
            "theorem branch(c: int32, x: int32, y: int32) {{ requires defined({expression}); ensures to_integer({expression}) == to_integer({expression}) by simp; }}"
        );
        verify_c0_sources(&source, &[]).unwrap();
        let invalid = source.replace(&format!("requires defined({expression});"), "");
        assert!(verify_c0_sources(&invalid, &[]).is_err());
        let one_branch = source.replace(
            &format!("requires defined({expression});"),
            "requires defined(x + 1);",
        );
        assert!(verify_c0_sources(&one_branch, &[]).is_err());
    }

    #[test]
    fn forward_conversion_aliases_retain_definedness() {
        for alias in [
            "let a: Integer = to_integer(x + 1);",
            "let b: Integer = to_integer(x + 1); let a: Integer = b + 0;",
        ] {
            let source = format!("theorem alias(x: int32) {{ {alias} ensures a == a by simp; }}");
            assert!(verify_c0_sources(&source, &[]).is_err(), "{source}");
            let bounded = source.replace("{ let", "{ requires defined(x + 1); let");
            verify_c0_sources(&bounded, &[]).unwrap();
        }
    }

    #[test]
    fn forward_conversion_memory_requires_ownership_and_definedness() {
        let c = "int32 read(int32* p) { return *p; }";
        let source = "verifying \"read.c\"; int32 read(int32* p) { owns p[0..1]; requires defined(p[0] + 1); ensures to_integer(p[0] + 1) == to_integer(p[0] + 1); } by { execute(); simp(); }";
        verify_c0_sources(source, &[("read.c", c)]).unwrap();
        for missing in ["owns p[0..1];", "requires defined(p[0] + 1);"] {
            let invalid = source.replace(missing, "");
            assert!(
                verify_c0_sources(&invalid, &[("read.c", c)]).is_err(),
                "{invalid}"
            );
        }
    }

    #[test]
    fn forward_conversion_keeps_intermediate_overflow_obligations() {
        let source = "theorem nested(x: int32) { requires defined((x + 1) + 1); ensures to_integer((x + 1) + 1) == to_integer((x + 1) + 1) by simp; }";
        verify_c0_sources(source, &[]).unwrap();
        let missing = source.replace("requires defined((x + 1) + 1);", "requires defined(x + 1);");
        assert!(verify_c0_sources(&missing, &[]).is_err());
        let cancelled = "theorem cancelled(x: int32) { ensures to_integer((x + 1) - 1) == to_integer((x + 1) - 1) by simp; }";
        assert!(verify_c0_sources(cancelled, &[]).is_err());
        let bounded = cancelled.replace("{ ensures", "{ requires defined((x + 1) - 1); ensures");
        verify_c0_sources(&bounded, &[]).unwrap();
    }

    #[test]
    fn forward_conversion_requires_symbolic_argument_definedness() {
        for proof in ["normalize()", "simp()"] {
            let source = format!(
                "theorem forward(x: int32) {{ ensures to_integer(x + 1) == to_integer(x + 1) by {{ {proof}; }} }}"
            );
            assert!(verify_c0_sources(&source, &[]).is_err(), "{source}");
            let bounded = source.replace("{ ensures", "{ requires defined(x + 1); ensures");
            verify_c0_sources(&bounded, &[])
                .unwrap_or_else(|error| panic!("{}\n{bounded}", error.message()));
            if proof == "simp()" {
                let expanded =
                    expand_c0_claim_source_by_label(&bounded, &[], "forward.ensures_0").unwrap();
                verify_c0_sources(&expanded, &[]).unwrap();
            }
        }
        let c = "int32 identity(int32 x) { return x; }";
        let source = "verifying \"identity.c\"; int32 identity(int32 x) { ensures to_integer(x + 1) == to_integer(x + 1); } by { execute(); simp(); }";
        assert!(verify_c0_sources(source, &[("identity.c", c)]).is_err());
        let bounded = source.replace("{ ensures", "{ requires defined(x + 1); ensures");
        verify_c0_sources(&bounded, &[("identity.c", c)]).unwrap();
    }

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
    fn integer_function_let_aliases_preserve_shared_expression_scaling() {
        let mut measured = Vec::new();
        for depth in [8, 16, 32, 64] {
            let mut source = String::from(
                "function f(x: Integer, y: Integer) -> Integer { x + y }\n\
                 theorem aliases(z: Integer) { let a0: Integer = z;\n",
            );
            for index in 1..=depth {
                source.push_str(&format!(
                    "let a{index}: Integer = f(a{}, a{});\n",
                    index - 1,
                    index - 1
                ));
            }
            source.push_str(&format!(
                "requires a{depth} == a{depth}; ensures a{depth} == a{depth} by {{ assumption(); }} }}"
            ));
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&source, &[])
            });
            result.unwrap_or_else(|error| panic!("depth {depth}: {}", error.message()));
            measured.push(work);
        }
        for pair in measured.windows(2) {
            assert!(
                pair[1] <= 3 * pair[0],
                "Integer aliases expanded: {measured:?}"
            );
        }
    }

    #[test]
    fn deferred_integer_function_high_arity_scales_with_arguments() {
        let mut measured = Vec::new();
        for arity in [8, 16, 32, 64] {
            let parameters = (0..arity)
                .map(|index| format!("x{index}: int32"))
                .collect::<Vec<_>>()
                .join(", ");
            let arguments = (0..arity)
                .map(|index| format!("x{index}"))
                .collect::<Vec<_>>()
                .join(", ");
            let source = format!(
                "function mix({parameters}) -> Integer {{ to_integer(x0) }}\n\
                 theorem call({parameters}) {{\n\
                 ensures mix({arguments}) == mix({arguments}) by {{ simp(); }} }}"
            );
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&source, &[])
            });
            result.unwrap_or_else(|error| panic!("arity {arity}: {}", error.message()));
            measured.push(work);
        }
        for pair in measured.windows(2) {
            assert!(
                pair[1] <= 3 * pair[0],
                "deferred arity expanded: {measured:?}"
            );
        }
    }

    #[test]
    fn deferred_integer_function_c_arguments_keep_mandatory_definedness() {
        let unguarded = "function f(x: int32) -> Integer { to_integer(x) }\n\
            theorem call(x: int32) { ensures f(x + 1) == f(x + 1) by simp; }";
        assert!(verify_c0_sources(unguarded, &[]).is_err());

        let guarded = unguarded.replace("{ ensures", "{ requires defined(x + 1); ensures");
        verify_c0_sources(&guarded, &[]).unwrap();
        let expanded = expand_c0_claim_source_by_label(&guarded, &[], "call.ensures_0").unwrap();
        verify_c0_sources(&expanded, &[]).unwrap();

        let mixed = "function mix(left: int32, right: int32) -> Integer { to_integer(left) }\n\
            theorem call(left: int32, right: int32) { requires defined(left + 1); requires defined(right + 1); ensures mix(left + 1, right + 1) == mix(left + 1, right + 1) by simp; }";
        verify_c0_sources(mixed, &[]).unwrap();
        for missing in [
            "requires defined(left + 1); ",
            "requires defined(right + 1); ",
        ] {
            let invalid = mixed.replacen(missing, "", 1);
            assert!(verify_c0_sources(&invalid, &[]).is_err(), "{invalid}");
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
    fn symbolic_integer_conversions_require_exact_bounds_for_all_targets() {
        for (target, lower, upper) in [
            ("int16", "-32768", "32767"),
            ("int32", "-2147483648", "2147483647"),
            ("uint8", "0", "255"),
            ("uint16", "0", "65535"),
            ("uint32", "0", "4294967295"),
            ("int64", "-9223372036854775808", "9223372036854775807"),
            ("uint64", "0", "18446744073709551615"),
        ] {
            let source = format!(
                "theorem conversion(z: Integer) {{ requires z >= {lower}; requires z <= {upper}; ensures to_{target}(z) == to_{target}(z) by simp; }}"
            );
            verify_c0_sources(&source, &[]).unwrap_or_else(|error| {
                panic!(
                    "bounded symbolic conversion `{target}` rejected: {}",
                    error.message()
                )
            });
        }
    }

    #[test]
    fn symbolic_integer_conversions_reject_missing_bounds() {
        for (target, lower, upper) in [
            ("int16", "-32768", "32767"),
            ("int32", "-2147483648", "2147483647"),
            ("uint8", "0", "255"),
            ("uint16", "0", "65535"),
            ("uint32", "0", "4294967295"),
            ("int64", "-9223372036854775808", "9223372036854775807"),
            ("uint64", "0", "18446744073709551615"),
        ] {
            for requirements in [
                vec![format!("z >= {lower}")],
                vec![format!("z <= {upper}")],
                Vec::new(),
            ] {
                let requires = requirements
                    .into_iter()
                    .map(|requirement| format!(" requires {requirement};"))
                    .collect::<String>();
                let source = format!(
                    "theorem conversion(z: Integer) {{{requires} ensures to_{target}(z) == to_{target}(z) by simp; }}"
                );
                assert!(
                    verify_c0_sources(&source, &[]).is_err(),
                    "conversion `{target}` accepted without both bounds: {source}"
                );
            }
        }
    }

    #[test]
    fn wrapped_symbolic_conversions_keep_bounds_through_proofs_and_expansion() {
        let bounded = "theorem wrapped(z: Integer) { requires z >= -2147483648; requires z <= 2147483647; ensures to_int32(z) + 0 == to_int32(z) by simp; }";
        verify_c0_sources(bounded, &[]).unwrap();
        let normalized = bounded.replace("by simp; }", "by { normalize(); } }");
        verify_c0_sources(&normalized, &[]).unwrap();
        let expanded = expand_c0_claim_source_by_label(bounded, &[], "wrapped.ensures_0").unwrap();
        verify_c0_sources(&expanded, &[]).unwrap();

        for missing in ["requires z >= -2147483648;", "requires z <= 2147483647;"] {
            let invalid = bounded.replace(missing, "");
            assert!(verify_c0_sources(&invalid, &[]).is_err(), "{invalid}");
        }

        let prior_have = "theorem prior(z: Integer) { requires z >= -2147483648; requires z <= 2147483647; let x: int32 = to_int32(z); ensures x + 0 == x by simp; }";
        verify_c0_sources(prior_have, &[]).unwrap();
        let aliases = "theorem aliases(z: Integer) { requires z >= -2147483648; requires z <= 2147483647; let a: int32 = to_int32(z); let b: int32 = a + 0; ensures b == a by simp; }";
        verify_c0_sources(aliases, &[]).unwrap();
        let no_bounds = "theorem aliases(z: Integer) { let a: int32 = to_int32(z); let b: int32 = a + 0; ensures b == a by simp; }";
        assert!(verify_c0_sources(no_bounds, &[]).is_err());
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
