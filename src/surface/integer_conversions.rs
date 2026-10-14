//! Public spelling and source types of explicit Integer conversions.
use super::*;

pub(super) fn integer_conversion_target(name: &str) -> Option<C0Type> {
    Some(match name {
        "to_int8" => C0Type::Int8,
        "to_int16" => C0Type::Int16,
        "to_int32" => C0Type::Int32,
        "to_uint8" => C0Type::UInt8,
        "to_uint16" => C0Type::UInt16,
        "to_uint32" => C0Type::UInt32,
        "to_int64" => C0Type::Int64(LongRank::Long),
        "to_uint64" => C0Type::UInt64(LongRank::Long),
        "to_int128" => C0Type::Int128,
        "to_uint128" => C0Type::UInt128,
        _ => return None,
    })
}

pub(super) fn is_integer_conversion(name: &str) -> bool {
    name == "to_integer" || integer_conversion_target(name).is_some()
}

pub(super) fn machine_integer_source_type(c_type: C0Type) -> bool {
    matches!(
        c_type,
        C0Type::Int8
            | C0Type::Int16
            | C0Type::Int32
            | C0Type::UInt8
            | C0Type::UInt16
            | C0Type::UInt32
            | C0Type::Int64(_)
            | C0Type::UInt64(_)
            | C0Type::Int128
            | C0Type::UInt128
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
    fn int32_remainder_bridge_requires_definedness_and_expands() {
        let source = "theorem remainder(a: int32, b: int32) { requires defined(a % b); requires to_integer(b) != 0; ensures to_integer(a % b) == truncating_remainder(to_integer(a), to_integer(b)) by { apply(int32_remainder_to_integer(a, b)) using { defined(a % b); to_integer(b) != 0; } } }";
        verify_c0_sources(source, &[]).unwrap();
        let expanded = expand_c0_claim_source_by_label(source, &[], "remainder.ensures_0").unwrap();
        verify_c0_sources(&expanded, &[]).unwrap();
        for requirement in ["requires defined(a % b);", "requires to_integer(b) != 0;"] {
            assert!(verify_c0_sources(&source.replace(requirement, ""), &[]).is_err());
        }
        for (a, b) in [("0", "0"), ("-2147483648", "-1")] {
            let invalid = format!(
                "theorem invalid() {{ ensures to_integer({a} % {b}) == 0 by {{ apply(int32_remainder_to_integer({a}, {b})); }} }}"
            );
            assert!(verify_c0_sources(&invalid, &[]).is_err());
        }
        let forged = "theorem int32_remainder_to_integer(a: int32, b: int32) { requires b != 0; requires to_integer(b) != 0; ensures to_integer(a % b) == truncating_remainder(to_integer(a), to_integer(b)); }";
        assert!(verify_c0_sources(forged, &[]).is_err());
    }

    #[test]
    fn uint32_product_bound_guard_expands_and_rejects_wrapped_or_signed_bounds() {
        let source = "theorem bounded(a: uint32, b: uint32) { requires to_integer(a) * to_integer(b) <= 4294967295; ensures b == 0u32 or a <= 4294967295u32 / b by { apply(uint32_multiply_guard_by_integer_bound(a, b)) using { to_integer(a) * to_integer(b) <= 4294967295; } } }";
        verify_c0_sources(source, &[]).unwrap();
        let expanded = expand_c0_claim_source_by_label(source, &[], "bounded.ensures_0").unwrap();
        verify_c0_sources(&expanded, &[]).unwrap();
        for requirement in [
            "to_integer(a * b) <= 4294967295",
            "to_integer((int32)a) * to_integer((int32)b) <= 4294967295",
            "to_integer(a) * to_integer(b) <= 4294967296",
        ] {
            let invalid =
                source.replace("to_integer(a) * to_integer(b) <= 4294967295", requirement);
            assert!(verify_c0_sources(&invalid, &[]).is_err(), "{invalid}");
        }
        let missing = source.replace("requires to_integer(a) * to_integer(b) <= 4294967295;", "");
        assert!(verify_c0_sources(&missing, &[]).is_err());
        let forged = "theorem uint32_multiply_guard_by_integer_bound(a: uint32, b: uint32) { requires to_integer(a) * to_integer(b) <= 4294967296; ensures b == 0u32 or a <= 4294967295u32 / b; }";
        assert!(verify_c0_sources(forged, &[]).is_err());
    }

    #[test]
    fn scalar_casts_keep_byte_read_width_in_definedness() {
        let c = "int32 read(const uint8* p) { return (int32)p[0]; }";
        let source = "verifying \"read.c\"; int32 read(const uint8* p) { views p[0..1]; ensures defined((int32)p[0]); } by { execute(); simp(); }";
        verify_c0_sources(source, &[("read.c", c)]).unwrap();
        let expanded =
            expand_c0_claim_source_by_label(source, &[("read.c", c)], "read.contract").unwrap();
        verify_c0_sources(&expanded, &[("read.c", c)]).unwrap();
        assert!(
            verify_c0_sources(
                &source.replace(
                    "ensures defined((int32)p[0])",
                    "ensures defined((int32)p[1])"
                ),
                &[("read.c", c)]
            )
            .is_err()
        );
    }

    #[test]
    fn integer_conversion_domains_survive_datatype_wrappers() {
        for value in [
            "Box::Wrapped(to_integer(x + 1))",
            "Outer::Wrapped(Box::Wrapped(to_integer(x + 1)))",
        ] {
            let source = format!(
                "spec enum Box {{ Wrapped(Integer) }} spec enum Outer {{ Wrapped(Box) }} theorem wrapped(x: int32) {{ ensures {value} == {value} by simp; }}"
            );
            assert!(verify_c0_sources(&source, &[]).is_err(), "{source}");
            let bounded = source.replace("{ ensures", "{ requires defined(x + 1); ensures");
            verify_c0_sources(&bounded, &[])
                .unwrap_or_else(|e| panic!("{}\n{bounded}", e.message()));
            let expanded =
                expand_c0_claim_source_by_label(&bounded, &[], "wrapped.ensures_0").unwrap();
            verify_c0_sources(&expanded, &[]).unwrap();
        }
    }

    #[test]
    fn integer_machine_round_trip_laws_require_both_bounds_and_expand() {
        for (target, lower, upper) in [
            ("int8", "-128", "127"),
            ("int16", "-32768", "32767"),
            ("int32", "-2147483648", "2147483647"),
            ("uint8", "0", "255"),
            ("uint16", "0", "65535"),
            ("uint32", "0", "4294967295"),
            ("int64", "-9223372036854775808", "9223372036854775807"),
            ("uint64", "0", "18446744073709551615"),
        ] {
            let source = format!(
                "theorem round_trip(z: Integer) {{ requires z >= {lower}; requires z <= {upper}; ensures to_integer(to_{target}(z)) == z by {{ apply(integer_to_{target}_round_trip(z)); }} }}"
            );
            verify_c0_sources(&source, &[]).unwrap_or_else(|e| panic!("{}\n{source}", e.message()));
            let expanded =
                expand_c0_claim_source_by_label(&source, &[], "round_trip.ensures_0").unwrap();
            verify_c0_sources(&expanded, &[]).unwrap();
            for missing in [
                format!("requires z >= {lower};"),
                format!("requires z <= {upper};"),
            ] {
                let invalid = source.replace(&missing, "");
                assert!(verify_c0_sources(&invalid, &[]).is_err(), "{invalid}");
            }
        }
    }

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
    fn uint32_small_remainder_expands_and_requires_strict_unsigned_evidence() {
        let source = "theorem lane(value: uint32, divisor: uint32) { requires value < divisor; ensures value % divisor == value by { apply(uint32_less_than_divisor_implies_remainder_is_value(value, divisor)); } }";
        verify_c0_sources(source, &[]).unwrap();
        let expanded = expand_c0_claim_source_by_label(source, &[], "lane.ensures_0").unwrap();
        verify_c0_sources(&expanded, &[]).unwrap();
        for invalid in [
            source.replace("requires value < divisor;", ""),
            source.replace("value < divisor", "value <= divisor"),
            source.replace("value < divisor", "divisor != 0u32"),
            source.replace("== value by", "== divisor by"),
            source.replace("is_value(value, divisor)", "is_value(divisor, value)"),
            source.replace("requires value < divisor;", "requires divisor == 0u32;"),
            expanded.replace("requires value < divisor;", ""),
            expanded.replace(
                "ensures value % divisor == value",
                "ensures value % divisor == divisor",
            ),
        ] {
            assert!(verify_c0_sources(&invalid, &[]).is_err(), "{invalid}");
        }
    }

    #[test]
    fn uint32_remainder_bound_expands_and_requires_a_nonzero_divisor() {
        let source = "theorem bridge(value: uint32, divisor: uint32) { requires divisor != 0u32; ensures to_integer(value % divisor) < to_integer(divisor) by { apply(uint32_remainder_less_than_divisor(value, divisor)); apply(uint32_less_than_to_integer(value % divisor, divisor)); } }";
        verify_c0_sources(source, &[]).unwrap();
        let expanded = expand_c0_claim_source_by_label(source, &[], "bridge.ensures_0").unwrap();
        verify_c0_sources(&expanded, &[]).unwrap();
        for invalid in [
            source.replace("requires divisor != 0u32;", ""),
            source.replace("requires divisor != 0u32;", "requires value != 0u32;"),
            source.replace("< to_integer(divisor) by", "< 65521 by"),
            source.replace("< to_integer(divisor) by", ">= to_integer(divisor) by"),
        ] {
            assert!(verify_c0_sources(&invalid, &[]).is_err(), "{invalid}");
        }
    }

    #[test]
    fn uint32_integer_bounds_do_not_distribute_wrapping_or_define_zero_division() {
        for invalid in [
            "theorem wrong(value: uint32) { ensures to_integer(value) <= 2147483647 by { apply(uint32_to_integer_bounds(value)); } }",
            "theorem wrong(value: uint32) { ensures to_integer(value + 1u32) == to_integer(value) + 1 by { apply(uint32_to_integer_bounds(value + 1u32)); } }",
            "theorem wrong(value: uint32) { ensures 0 <= to_integer(value / 0u32) by { apply(uint32_to_integer_bounds(value / 0u32)); } }",
        ] {
            assert!(verify_c0_sources(invalid, &[]).is_err(), "{invalid}");
        }
    }

    #[test]
    fn uint32_integer_order_bridges_recheck_expansion_and_require_evidence() {
        for (name, premise, conclusion) in [
            (
                "uint32_less_equal_to_integer",
                "left <= right",
                "to_integer(left) <= to_integer(right)",
            ),
            (
                "uint32_to_integer_less_equal_implies_less_equal",
                "to_integer(left) <= to_integer(right)",
                "left <= right",
            ),
            (
                "uint32_to_integer_equal_implies_equal",
                "to_integer(left) == to_integer(right)",
                "left == right",
            ),
        ] {
            let source = format!(
                "theorem bridge(left: uint32, right: uint32) {{ requires {premise}; ensures {conclusion} by {{ apply({name}(left, right)); }} }}"
            );
            verify_c0_sources(&source, &[]).unwrap();
            let expanded =
                expand_c0_claim_source_by_label(&source, &[], "bridge.ensures_0").unwrap();
            verify_c0_sources(&expanded, &[]).unwrap();
            for invalid in [
                source.replace(&format!("requires {premise};"), ""),
                source.replace("ensures", "ensures not"),
                source.replace(
                    &format!("{name}(left, right)"),
                    &format!("{name}(right, left)"),
                ),
            ] {
                assert!(verify_c0_sources(&invalid, &[]).is_err(), "{invalid}");
            }
        }
    }

    #[test]
    fn integer_order_observation_requires_the_c_guard_and_rechecks_expansion() {
        let source = "theorem bridge(left: int32, right: int32) { requires left <= right; ensures to_integer(left) <= to_integer(right) by { apply(int32_less_equal_to_integer(left, right)); } }";
        verify_c0_sources(source, &[]).unwrap();
        let expanded = expand_c0_claim_source_by_label(source, &[], "bridge.ensures_0").unwrap();
        verify_c0_sources(&expanded, &[]).unwrap();

        for invalid in [
            source.replace("requires left <= right;", ""),
            source.replace("requires left <= right;", "requires right <= left;"),
        ] {
            assert!(
                verify_c0_sources(&invalid, &[]).is_err(),
                "order observation accepted an invalid guard: {invalid}"
            );
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
    fn symbolic_integer_datatype_matches_are_exhaustive_and_checked() {
        let source = "spec enum Box<T> { Empty, Wrapped(T), }\n            function project(value: Box<Integer>) -> Integer { match value { Box::Empty => to_integer(0), Box::Wrapped(inner) => inner, } }\n\
            theorem symbolic(value: Box<Integer>) { ensures project(value) == project(value) by simp; }";
        verify_c0_sources(source, &[]).unwrap();
        let expanded = expand_c0_claim_source_by_label(source, &[], "symbolic.ensures_0").unwrap();
        verify_c0_sources(&expanded, &[]).unwrap();
    }

    #[test]
    fn integer_datatype_match_reduces_known_constructor() {
        let source = r#"
            spec enum Box { Empty, Wrapped(Integer), }
            function project(value: Box) -> Integer { match value { Box::Empty => to_integer(0), Box::Wrapped(inner) => inner, } }
            theorem known() { ensures project(Box::Wrapped(to_integer(7))) == to_integer(7) by simp; }
        "#;
        verify_c0_sources(source, &[]).unwrap();
        let expanded = expand_c0_claim_source_by_label(source, &[], "known.ensures_0").unwrap();
        verify_c0_sources(&expanded, &[]).unwrap();
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
    fn deferred_integer_function_argument_domains_cover_division_and_branches() {
        for proof in ["simp()", "normalize()"] {
            let division = format!(
                "function f(x: int32) -> Integer {{ to_integer(x) }}\n\
                 theorem call(x: int32) {{ ensures f(1 / x) == f(1 / x) by {{ {proof}; }} }}"
            );
            assert!(verify_c0_sources(&division, &[]).is_err(), "{division}");
            let guarded = division.replace("{ ensures", "{ requires x != 0; ensures");
            verify_c0_sources(&guarded, &[]).unwrap();
            let expanded =
                expand_c0_claim_source_by_label(&guarded, &[], "call.ensures_0").unwrap();
            verify_c0_sources(&expanded, &[]).unwrap();

            let branch = format!(
                "function f(x: int32) -> Integer {{ to_integer(x) }}\n\
                 theorem call(c: int32, x: int32, y: int32) {{ ensures f(if c == 0 {{ x + 1 }} else {{ y + 1 }}) == f(if c == 0 {{ x + 1 }} else {{ y + 1 }}) by {{ {proof}; }} }}"
            );
            assert!(verify_c0_sources(&branch, &[]).is_err(), "{branch}");
            let guarded = branch.replace(
                "{ ensures",
                "{ requires defined(if c == 0 { x + 1 } else { y + 1 }); ensures",
            );
            verify_c0_sources(&guarded, &[]).unwrap();
            let expanded =
                expand_c0_claim_source_by_label(&guarded, &[], "call.ensures_0").unwrap();
            verify_c0_sources(&expanded, &[]).unwrap();
        }
    }

    #[test]
    fn deferred_integer_function_argument_domains_cross_algebraic_wrappers() {
        let source = "spec enum Box { Empty, Wrapped(int32), }\n\
            function pack(x: int32) -> Box { Box::Wrapped(x) }\n\
            function f(value: Box) -> Integer { 0 }\n\
            theorem call(x: int32) { ensures f(pack(x + 1)) == f(pack(x + 1)) by simp; }";
        assert!(verify_c0_sources(source, &[]).is_err());
        let guarded = source.replace("{ ensures", "{ requires defined(x + 1); ensures");
        verify_c0_sources(&guarded, &[]).unwrap();
        let expanded = expand_c0_claim_source_by_label(&guarded, &[], "call.ensures_0").unwrap();
        verify_c0_sources(&expanded, &[]).unwrap();
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
    fn wide_integer_observations_and_checked_conversions_expand_and_recheck() {
        for source in [
            "theorem observe(x: int128) { ensures to_integer(x) == to_integer(x) by simp; }",
            "theorem observe(x: uint128) { ensures to_integer(x) == to_integer(x) by simp; }",
            "theorem observe() { ensures to_integer(to_int128(-170141183460469231731687303715884105728)) == -170141183460469231731687303715884105728 by simp; }",
            "theorem observe() { ensures to_integer(to_int128(170141183460469231731687303715884105727)) == 170141183460469231731687303715884105727 by simp; }",
            "theorem observe() { ensures to_integer(to_uint128(340282366920938463463374607431768211455)) == 340282366920938463463374607431768211455 by simp; }",
        ] {
            verify_c0_sources(source, &[])
                .unwrap_or_else(|error| panic!("{}\n{source}", error.message()));
            let expanded =
                expand_c0_claim_source_by_label(source, &[], "observe.ensures_0").unwrap();
            verify_c0_sources(&expanded, &[])
                .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
        }
        for (target, value) in [
            ("int128", "-170141183460469231731687303715884105729"),
            ("int128", "170141183460469231731687303715884105728"),
            ("uint128", "-1"),
            ("uint128", "340282366920938463463374607431768211456"),
        ] {
            let source = format!(
                "theorem bad() {{ ensures to_integer(to_{target}({value})) == {value} by simp; }}"
            );
            assert!(verify_c0_sources(&source, &[]).is_err(), "{source}");
        }
        for (target, lower, upper) in [
            (
                "int128",
                "-170141183460469231731687303715884105728",
                "170141183460469231731687303715884105727",
            ),
            ("uint128", "0", "340282366920938463463374607431768211455"),
        ] {
            for (requirements, valid) in [
                (
                    format!("requires z >= {lower}; requires z <= {upper};"),
                    true,
                ),
                (format!("requires z >= {lower};"), false),
                (format!("requires z <= {upper};"), false),
                (String::new(), false),
            ] {
                let source = format!(
                    "theorem observe(z: Integer) {{ {requirements} ensures to_integer(to_{target}(z)) == to_integer(to_{target}(z)) by simp; }}"
                );
                assert_eq!(verify_c0_sources(&source, &[]).is_ok(), valid, "{source}");
            }
        }
    }

    #[test]
    fn integer_conversion_rejects_each_out_of_range_boundary() {
        for (target, lower, upper) in [
            ("int8", "-129", "128"),
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
            ("int8", "-128", "127"),
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
            ("int8", "-128", "127"),
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
    #[test]
    fn legacy_integer_cast_identity_preserves_field_views_and_snapshot_observations() {
        for (field, destination, lower, upper) in [
            ("fee", "uint64", "0", "8589934591"),
            ("size", "uint32", "1", "2147483647"),
        ] {
            let c = format!(
                "struct FeeFrac {{ int64 fee; int32 size; }}; {destination} cast(const struct FeeFrac* self) {{ return ({destination})self->{field}; }}"
            );
            let source = format!(
                r#"verifying "cast.c";
{destination} cast(const struct FeeFrac* self) {{
    views self->{field};
    requires {lower} <= to_integer(self->{field});
    requires to_integer(self->{field}) <= {upper};
    ensures to_integer(result) == to_integer(old(self->{field}));
    ensures self->{field} == old(self->{field});
}} by {{
    execute();
    have to_integer(result) == to_integer(self->{field}) by {{ arithmetic_certificate rules {{
        premise 0: {lower} <= to_integer(self->{field}) => {lower} <= to_integer(self->{field});
        premise 1: to_integer(self->{field}) <= {upper} => to_integer(self->{field}) <= {upper};
        integer_cast_identity bounds [0, 1] => to_integer(result) == to_integer(self->{field}); conclusion 0;
    }} }}
    simp();
}}
"#
            );
            verify_c0_sources(&source, &[("cast.c", &c)])
                .unwrap_or_else(|e| panic!("{field}: {}", e.message()));
            let expanded =
                expand_c0_claim_source_by_label(&source, &[("cast.c", &c)], "cast.ensures_0")
                    .unwrap();
            verify_c0_sources(&expanded, &[("cast.c", &c)]).unwrap();
            assert!(
                verify_c0_sources(
                    &source.replace(&format!("views self->{field};"), ""),
                    &[("cast.c", &c)]
                )
                .is_err()
            );
        }
    }

    #[test]
    #[ignore = "nightly: 1.5s in the parallel gate"]
    fn legacy_integer_cast_identity_verifies_c_callers_and_rechecks_bounds_and_expansion() {
        for (source_ty, destination, lower, upper, native_guard) in [
            ("int64", "uint64", "0", "9223372036854775807", ""),
            ("int32", "uint64", "0", "2147483647", ""),
            ("int32", "uint32", "0", "2147483647", ""),
            ("uint32", "uint64", "0", "4294967295", ""),
            (
                "uint64",
                "int64",
                "0",
                "9223372036854775807",
                "requires value <= 9223372036854775807u64;",
            ),
            ("uint64", "uint32", "0", "4294967295", ""),
        ] {
            let c = format!(
                "{destination} cast({source_ty} value) {{ return ({destination})value; }} {destination} caller({source_ty} value) {{ return cast(value); }}"
            );
            let contract = format!(
                "{native_guard} requires {lower} <= to_integer(value); requires to_integer(value) <= {upper}; ensures to_integer(result) == to_integer(value);"
            );
            let source = format!(
                r#"verifying "cast.c";
{destination} cast({source_ty} value) {{ {contract} }} by {{
    execute();
    arithmetic_certificate rules {{
        premise 0: {lower} <= to_integer(value) => {lower} <= to_integer(value);
        premise 1: to_integer(value) <= {upper} => to_integer(value) <= {upper};
        integer_cast_identity bounds [0, 1] => to_integer(result) == to_integer(value); conclusion 0;
    }}
}}
{destination} caller({source_ty} value) {{ {contract} }} by {{ execute(); simp(); }}
"#
            );
            verify_c0_sources(&source, &[("cast.c", &c)])
                .unwrap_or_else(|e| panic!("{source_ty}/{destination}: {}", e.message()));
            if source_ty == "uint64" && destination == "int64" {
                let implicit_return = c.replace("return (int64)value;", "return value;");
                verify_c0_sources(&source, &[("cast.c", &implicit_return)]).unwrap();
                let expanded = expand_c0_claim_source_by_label(
                    &source,
                    &[("cast.c", &implicit_return)],
                    "cast.ensures_0",
                )
                .unwrap();
                verify_c0_sources(&expanded, &[("cast.c", &implicit_return)]).unwrap();
            }
            // C's conversion owes no native range; the Integer bounds the
            // certificate cites alone justify the identity.
            if !native_guard.is_empty() {
                verify_c0_sources(&source.replace(native_guard, ""), &[("cast.c", &c)])
                    .unwrap_or_else(|e| panic!("{source_ty}/{destination}: {}", e.message()));
            }
            let expanded =
                expand_c0_claim_source_by_label(&source, &[("cast.c", &c)], "caller.ensures_0")
                    .unwrap();
            verify_c0_sources(&expanded, &[("cast.c", &c)]).unwrap();
            for invalid in [
                source.replace(&format!("requires {lower} <= to_integer(value);"), ""),
                source.replace(&format!("requires to_integer(value) <= {upper};"), ""),
                source.replace(
                    "integer_cast_identity bounds [0, 1]",
                    "integer_cast_identity bounds [1, 0]",
                ),
                source.replace(
                    "integer_cast_identity bounds [0, 1]",
                    "integer_cast_identity bounds [0, 0]",
                ),
                source.replace(
                    "to_integer(result) == to_integer(value)",
                    "to_integer(result) == to_integer(value) + 1",
                ),
            ] {
                assert!(
                    verify_c0_sources(&invalid, &[("cast.c", &c)]).is_err(),
                    "{source_ty}/{destination}"
                );
            }
        }
    }

    #[test]
    fn uint32_subtract_bridge_rechecks_guards_and_expansion() {
        let source = "theorem exact(left: uint32, right: uint32) { requires right <= left; ensures to_integer(left - right) == to_integer(left) - to_integer(right) by { apply(uint32_subtract_to_integer(left, right)) using { right <= left; } } }";
        verify_c0_sources(source, &[]).unwrap();
        let expanded = expand_c0_claim_source_by_label(source, &[], "exact.ensures_0").unwrap();
        verify_c0_sources(&expanded, &[]).unwrap();
        for invalid in [
            source.replace("requires right <= left;", ""),
            source.replace("requires right <= left;", "requires defined(left - right);"),
            source.replace("requires right <= left;", "requires left <= right;"),
            source.replace("using { right <= left; }", "using {}"),
            source.replace(
                "to_integer(left) - to_integer(right) by",
                "to_integer(left) + to_integer(right) by",
            ),
        ] {
            assert!(verify_c0_sources(&invalid, &[]).is_err(), "{invalid}");
        }
        for (left, right, difference) in [
            (0u32, 0u32, 0u32),
            (65521, 65520, 1),
            (0x8000_0000, 1, 0x7fff_ffff),
            (u32::MAX, 0, u32::MAX),
            (u32::MAX, 0x8000_0000, 0x7fff_ffff),
        ] {
            let concrete = format!(
                "theorem boundary() {{ ensures to_integer({left}u32 - {right}u32) == {difference} by {{ apply(uint32_subtract_to_integer({left}u32, {right}u32)); simp(); }} }}"
            );
            verify_c0_sources(&concrete, &[]).unwrap();
        }
        let underflow = "theorem wrapping() { ensures to_integer(0u32 - 1u32) == -1 by { apply(uint32_subtract_to_integer(0u32, 1u32)); } }";
        assert!(verify_c0_sources(underflow, &[]).is_err());
    }

    #[test]
    fn uint32_subtract_bridge_verifies_executed_c_difference() {
        let c = "unsigned int difference(unsigned int left, unsigned int right) { return left - right; }";
        let source = "verifying \"difference.c\"; uint32 difference(uint32 left, uint32 right) { requires right <= left; ensures to_integer(result) == to_integer(left) - to_integer(right); } by { execute(); apply(uint32_subtract_to_integer(left, right)) using { right <= left; } simp(); }";
        verify_c0_sources(source, &[("difference.c", c)]).unwrap();
        let expanded =
            expand_c0_claim_source_by_label(source, &[("difference.c", c)], "difference.contract")
                .unwrap();
        verify_c0_sources(&expanded, &[("difference.c", c)]).unwrap();
        for invalid in [
            source.replace("requires right <= left;", ""),
            source.replace("requires right <= left;", "requires defined(left - right);"),
            source.replace(
                "ensures to_integer(result) == to_integer(left) - to_integer(right);",
                "ensures to_integer(result) == to_integer(right) - to_integer(left);",
            ),
        ] {
            assert!(
                verify_c0_sources(&invalid, &[("difference.c", c)]).is_err(),
                "{invalid}"
            );
        }
    }

    #[test]
    #[ignore = "nightly: 0.9s in the parallel gate"]
    fn uint64_integer_bridges_recheck_guards_full_width_and_expansion() {
        for (name, guard, goal) in [
            (
                "uint64_add_to_integer",
                "to_integer(left) + to_integer(right) <= 18446744073709551615",
                "to_integer(left + right) == to_integer(left) + to_integer(right)",
            ),
            (
                "uint64_multiply_to_integer",
                "to_integer(left) * to_integer(right) <= 18446744073709551615",
                "to_integer(left * right) == to_integer(left) * to_integer(right)",
            ),
            (
                "uint64_subtract_to_integer",
                "to_integer(right) <= to_integer(left)",
                "to_integer(left - right) == to_integer(left) - to_integer(right)",
            ),
            (
                "uint64_divide_to_integer",
                "right != 0u64; requires to_integer(right) != 0",
                "to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right))",
            ),
            (
                "uint64_remainder_to_integer",
                "right != 0u64; requires to_integer(right) != 0",
                "to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right))",
            ),
            (
                "uint64_less_equal_to_integer",
                "left <= right",
                "to_integer(left) <= to_integer(right)",
            ),
            (
                "uint64_to_integer_less_equal_implies_less_equal",
                "to_integer(left) <= to_integer(right)",
                "left <= right",
            ),
            (
                "uint64_less_than_to_integer",
                "left < right",
                "to_integer(left) < to_integer(right)",
            ),
            (
                "uint64_to_integer_less_than_implies_less_than",
                "to_integer(left) < to_integer(right)",
                "left < right",
            ),
        ] {
            let source = format!(
                "theorem bridge(left: uint64, right: uint64) {{ requires {guard}; ensures {goal} by {{ apply({name}(left, right)); }} }}"
            );
            verify_c0_sources(&source, &[]).unwrap_or_else(|e| panic!("{name}: {}", e.message()));
            let expanded =
                expand_c0_claim_source_by_label(&source, &[], "bridge.ensures_0").unwrap();
            verify_c0_sources(&expanded, &[]).unwrap();
            for invalid in [
                source.replace(&format!("requires {guard};"), ""),
                source.replace(
                    &format!("requires {guard};"),
                    "requires defined(left + right);",
                ),
                source.replace("left: uint64", "left: int64"),
                source.replace("right: uint64", "right: uint32"),
                source.replace(&format!("ensures {goal}"), "ensures left > right"),
            ] {
                assert!(verify_c0_sources(&invalid, &[]).is_err(), "{invalid}");
            }
        }
    }

    // Both native operations and modular calls must preserve the mathematical
    // observation; omitting either evaluation domain must not prove a claim.
    #[test]
    fn uint32_division_bridges_verify_actual_operations_calls_and_expansion() {
        for (name, op, mathematical) in [
            ("uint32_divide_to_integer", "/", "truncating_quotient"),
            ("uint32_remainder_to_integer", "%", "truncating_remainder"),
        ] {
            let guard = "right != 0u32; requires to_integer(right) != 0";
            let goal = format!(
                "to_integer(result) == {mathematical}(to_integer(left), to_integer(right))"
            );
            let c = format!(
                "uint32 op(uint32 left, uint32 right) {{ return left {op} right; }} uint32 caller(uint32 left, uint32 right) {{ return op(left, right); }}"
            );
            let source = format!(
                "verifying \"op.c\"; uint32 op(uint32 left, uint32 right) {{ requires {guard}; ensures {goal}; }} by {{ apply({name}(left, right)); execute(); simp(); }} uint32 caller(uint32 left, uint32 right) {{ requires {guard}; ensures {goal}; }} by {{ execute(); simp(); }}"
            );
            verify_c0_sources(&source, &[("op.c", &c)])
                .unwrap_or_else(|error| panic!("{}\n{source}", error.message()));
            let expanded =
                expand_c0_claim_source_by_label(&source, &[("op.c", &c)], "op.ensures_0").unwrap();
            verify_c0_sources(&expanded, &[("op.c", &c)]).unwrap();
            for missing in [
                "requires right != 0u32;",
                "requires to_integer(right) != 0;",
            ] {
                assert!(verify_c0_sources(&source.replace(missing, ""), &[("op.c", &c)]).is_err());
            }
            assert!(
                verify_c0_sources(
                    &source.replace(&format!("ensures {goal};"), &format!("ensures {goal} + 1;")),
                    &[("op.c", &c)]
                )
                .is_err()
            );
        }
    }

    #[test]
    fn uint64_division_bridges_require_both_evaluation_domains() {
        for (name, op, mathematical) in [
            ("uint64_divide_to_integer", "/", "truncating_quotient"),
            ("uint64_remainder_to_integer", "%", "truncating_remainder"),
        ] {
            let source = format!(
                "theorem exact(left: uint64, right: uint64) {{ requires right != 0u64; requires to_integer(right) != 0; ensures to_integer(left {op} right) == {mathematical}(to_integer(left), to_integer(right)) by {{ apply({name}(left, right)); }} }}"
            );
            verify_c0_sources(&source, &[]).unwrap();
            for missing in [
                "requires right != 0u64;",
                "requires to_integer(right) != 0;",
            ] {
                assert!(verify_c0_sources(&source.replace(missing, ""), &[]).is_err());
            }
        }
    }

    #[test]
    #[ignore = "nightly: 0.8s in the parallel gate"]
    fn uint64_integer_bridges_verify_actual_c_operations_and_modular_calls() {
        for (name, guard, goal, op) in [
            (
                "uint64_add_to_integer",
                "to_integer(left) + to_integer(right) <= 18446744073709551615",
                "to_integer(left + right) == to_integer(left) + to_integer(right)",
                "+",
            ),
            (
                "uint64_multiply_to_integer",
                "to_integer(left) * to_integer(right) <= 18446744073709551615",
                "to_integer(left * right) == to_integer(left) * to_integer(right)",
                "*",
            ),
            (
                "uint64_subtract_to_integer",
                "to_integer(right) <= to_integer(left)",
                "to_integer(left - right) == to_integer(left) - to_integer(right)",
                "-",
            ),
            (
                "uint64_divide_to_integer",
                "right != 0u64; requires to_integer(right) != 0",
                "to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right))",
                "/",
            ),
            (
                "uint64_remainder_to_integer",
                "right != 0u64; requires to_integer(right) != 0",
                "to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right))",
                "%",
            ),
        ] {
            let c = format!(
                "uint64 op(uint64 left, uint64 right) {{ return left {op} right; }} uint64 caller(uint64 left, uint64 right) {{ return op(left, right); }}"
            );
            let result_goal = goal.replace(
                &format!("to_integer(left {op} right)"),
                "to_integer(result)",
            );
            let source = format!(
                "verifying \"op.c\"; uint64 op(uint64 left, uint64 right) {{ requires {guard}; ensures {result_goal}; }} by {{ apply({name}(left, right)); execute(); simp(); }} uint64 caller(uint64 left, uint64 right) {{ requires {guard}; ensures {result_goal}; }} by {{ execute(); simp(); }}"
            );
            verify_c0_sources(&source, &[("op.c", &c)])
                .unwrap_or_else(|e| panic!("{name}: {}", e.message()));
            let expanded =
                expand_c0_claim_source_by_label(&source, &[("op.c", &c)], "op.ensures_0").unwrap();
            verify_c0_sources(&expanded, &[("op.c", &c)]).unwrap();
            assert!(
                verify_c0_sources(
                    &source.replace(&format!("requires {guard};"), ""),
                    &[("op.c", &c)]
                )
                .is_err()
            );
        }
    }

    #[test]
    fn signed_integer_order_bridges_recheck_source_guards_and_expansion() {
        for (name, ty, guard, goal) in [
            (
                "int32_to_integer_less_equal_implies_less_equal",
                "int32",
                "to_integer(left) <= to_integer(right)",
                "left <= right",
            ),
            (
                "int64_less_equal_to_integer",
                "int64",
                "left <= right",
                "to_integer(left) <= to_integer(right)",
            ),
            (
                "int64_less_than_to_integer",
                "int64",
                "left < right",
                "to_integer(left) < to_integer(right)",
            ),
            (
                "int64_greater_equal_to_integer",
                "int64",
                "left >= right",
                "to_integer(left) >= to_integer(right)",
            ),
            (
                "int64_to_integer_less_equal_implies_less_equal",
                "int64",
                "to_integer(left) <= to_integer(right)",
                "left <= right",
            ),
            (
                "int64_to_integer_equal_implies_equal",
                "int64",
                "to_integer(left) == to_integer(right)",
                "left == right",
            ),
        ] {
            let source = format!(
                "theorem bridge(left: {ty}, right: {ty}) {{ requires {guard}; ensures {goal} by {{ apply({name}(left, right)); }} }}"
            );
            verify_c0_sources(&source, &[]).unwrap();
            let expanded =
                expand_c0_claim_source_by_label(&source, &[], "bridge.ensures_0").unwrap();
            verify_c0_sources(&expanded, &[]).unwrap();
            for invalid in [
                source.replace(&format!("requires {guard};"), ""),
                source.replace(&format!("ensures {goal}"), "ensures left > right"),
            ] {
                assert!(verify_c0_sources(&invalid, &[]).is_err());
            }
        }
    }

    #[test]
    #[ignore = "nightly: 1.9s in the parallel gate"]
    fn machine_integer_order_bridge_applications_scale_with_steps_and_unused_bounds() {
        for ty in ["int32", "int64", "uint64"] {
            let mut samples = Vec::new();
            for size in [4usize, 16, 64, 256] {
                let mut source = format!(
                    "theorem bridge(x: {ty}, y: {ty}, z: {ty}) {{ requires to_integer(x) <= to_integer(y); "
                );
                for i in 0..size {
                    source.push_str(&format!("requires to_integer(z) <= {i}; "));
                }
                source.push_str("ensures x <= y by { ");
                for _ in 0..size {
                    source.push_str(&format!("have x <= y by {{ apply({ty}_to_integer_less_equal_implies_less_equal(x, y)) using {{ to_integer(x) <= to_integer(y); }} }} "));
                }
                source.push_str("assumption(); } }");
                let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                    verify_c0_sources(&source, &[])
                });
                result.unwrap_or_else(|error| panic!("{ty}/{size}: {}", error.message()));
                samples.push(work);
            }
            for pair in samples.windows(2) {
                assert!(
                    pair[1] <= pair[0] * 6,
                    "bridge work grew faster than the proof: {ty}: {samples:?}"
                );
            }
        }
    }
    #[test]
    fn contract_scalar_casts_check_all_supported_widths_and_recheck_expansion() {
        for ty in ["int32", "uint32", "int64", "uint64", "int128", "uint128"] {
            let source = format!(
                "theorem cast(x: {ty}) {{ ensures ({ty})x == x by {{ have ({ty})x == x by simp; assumption(); }} }}"
            );
            verify_c0_sources(&source, &[]).unwrap();
            let expanded = expand_c0_claim_source_by_label(&source, &[], "cast.ensures_0").unwrap();
            verify_c0_sources(&expanded, &[]).unwrap();
            for invalid in [
                source.replace(&format!("({ty})x"), &format!("({ty}*)x")),
                source.replace(&format!("x: {ty}"), "x: Integer"),
                source.replace(&format!("({ty})x"), &format!("({ty})old(x)")),
                source.replace("== x", "!= x"),
            ] {
                assert!(verify_c0_sources(&invalid, &[]).is_err(), "{invalid}");
            }
        }
    }
    #[test]
    fn int64_integer_operation_applications_recheck_guards_and_expansion() {
        for (name, op) in [
            ("int64_add_to_integer", "+"),
            ("int64_subtract_to_integer", "-"),
        ] {
            let source = format!(
                "theorem exact(left: int64, right: int64) {{ requires defined(left {op} right); ensures to_integer(left {op} right) == to_integer(left) {op} to_integer(right) by {{ apply({name}(left, right)); }} }}"
            );
            verify_c0_sources(&source, &[]).unwrap();
            let expanded =
                expand_c0_claim_source_by_label(&source, &[], "exact.ensures_0").unwrap();
            verify_c0_sources(&expanded, &[]).unwrap();
            for invalid in [
                source.replace(&format!("requires defined(left {op} right);"), ""),
                source.replace(" == ", " != "),
            ] {
                assert!(verify_c0_sources(&invalid, &[]).is_err(), "{invalid}");
            }
        }
    }
    #[test]
    #[ignore = "nightly: 1.7s in the parallel gate"]
    fn int64_integer_operation_applications_scale_with_steps_and_unused_bounds() {
        for (name, op) in [
            ("int64_add_to_integer", "+"),
            ("int64_subtract_to_integer", "-"),
        ] {
            let guard = format!("defined(x {op} y)");
            let goal = format!("to_integer(x {op} y) == to_integer(x) {op} to_integer(y)");
            let mut samples = Vec::new();
            for size in [4usize, 16, 64, 256] {
                let mut source =
                    format!("theorem exact(x: int64, y: int64, z: int64) {{ requires {guard}; ");
                for i in 0..size {
                    source.push_str(&format!("requires to_integer(z) <= {i}; "));
                }
                source.push_str(&format!("ensures {goal} by {{ "));
                for _ in 0..size {
                    source.push_str(&format!(
                        "have {goal} by {{ apply({name}(x, y)) using {{ {guard}; }} }} "
                    ));
                }
                source.push_str("assumption(); } }");
                let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                    verify_c0_sources(&source, &[])
                });
                result.unwrap_or_else(|error| panic!("{name}/{size}: {}", error.message()));
                samples.push(work);
            }
            for pair in samples.windows(2) {
                assert!(pair[1] <= pair[0] * 6, "{name}: {samples:?}");
            }
        }
    }
    #[test]
    #[ignore = "nightly: 0.8s in the parallel gate"]
    fn rounded_integer_library_derivations_expand_and_reverify() {
        let fixture = include_str!("../../mdtests/integer_rounded_product_bounds.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        verify_c0_sources(source, &[]).unwrap();
        for label in [
            "derived_floor_from_remainder.ensures_0",
            "derived_floor_from_remainder.ensures_1",
            "derived_ceiling_from_remainder.ensures_0",
            "derived_ceiling_from_remainder.ensures_1",
        ] {
            let expanded = expand_c0_claim_source_by_label(source, &[], label).unwrap();
            verify_c0_sources(&expanded, &[]).unwrap();
        }
    }

    #[test]
    #[ignore = "nightly: 0.8s in the parallel gate"]
    fn opaque_product_arithmetic_scales_with_steps_and_unused_bounds() {
        let goal = "q * d <= n";
        let mut samples = Vec::new();
        for size in [4usize, 16, 64, 256] {
            let mut source = String::from(
                "theorem bound(n: Integer, q: Integer, d: Integer, r: Integer, z: Integer) { requires n == q * d + r; requires 0 <= r; ",
            );
            for i in 0..size {
                source.push_str(&format!("requires z <= {i}; "));
            }
            source.push_str(&format!("ensures {goal} by {{ "));
            for _ in 0..size {
                source.push_str(&format!(
                    "have {goal} by {{ arithmetic() using {{ n == q * d + r; 0 <= r; }} }} "
                ));
            }
            source.push_str("assumption(); } }");
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&source, &[])
            });
            result.unwrap_or_else(|error| panic!("{size}: {}", error.message()));
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(pair[1] <= pair[0] * 6, "{samples:?}");
        }
    }

    #[test]
    fn integer_multiply_add_rechecks_application_and_expansion() {
        let source = "theorem distribute(a: Integer, b: Integer, c: Integer) { ensures (a + b) * c == a * c + b * c by { apply(integer_multiply_add(a, b, c)); } }";
        verify_c0_sources(source, &[]).unwrap();
        let expanded =
            expand_c0_claim_source_by_label(source, &[], "distribute.ensures_0").unwrap();
        verify_c0_sources(&expanded, &[]).unwrap();
        for invalid in [
            source.replace("a * c + b * c", "a * c + b"),
            source.replace("multiply_add(a, b, c)", "multiply_add(a, c, b)"),
            source.replace("multiply_add(a, b, c)", "multiply_add(a, b)"),
            source.replace(": Integer", ": int32"),
        ] {
            assert!(verify_c0_sources(&invalid, &[]).is_err(), "{invalid}");
        }
    }

    #[test]
    #[ignore = "nightly: 0.5s in the parallel gate"]
    fn integer_multiply_add_applications_scale_with_steps_and_unused_bounds() {
        let goal = "(a + b) * c == a * c + b * c";
        let mut samples = Vec::new();
        for size in [4usize, 16, 64, 256] {
            let mut source = String::from(
                "theorem distribute(a: Integer, b: Integer, c: Integer, z: Integer) { ",
            );
            for i in 0..size {
                source.push_str(&format!("requires z <= {i}; "));
            }
            source.push_str(&format!("ensures {goal} by {{ "));
            for _ in 0..size {
                source.push_str(&format!(
                    "have {goal} by {{ apply(integer_multiply_add(a, b, c)); }} "
                ));
            }
            source.push_str("assumption(); } }");
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&source, &[])
            });
            result.unwrap_or_else(|error| panic!("{size}: {}", error.message()));
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(pair[1] <= pair[0] * 6, "{samples:?}");
        }
    }

    #[test]
    fn integer_truncation_applications_recheck_guards_claims_and_expansion() {
        for (name, requirements, goal) in [
            (
                "integer_truncation_identity",
                &["d != 0"][..],
                "n == truncating_quotient(n, d) * d + truncating_remainder(n, d)",
            ),
            (
                "integer_positive_divisor_remainder_lower",
                &["d != 0", "0 < d"][..],
                "1 - d <= truncating_remainder(n, d)",
            ),
            (
                "integer_positive_divisor_remainder_upper",
                &["d != 0", "0 < d"][..],
                "truncating_remainder(n, d) <= d - 1",
            ),
            (
                "integer_nonnegative_dividend_remainder",
                &["d != 0", "0 <= n"][..],
                "0 <= truncating_remainder(n, d)",
            ),
            (
                "integer_nonpositive_dividend_remainder",
                &["d != 0", "n <= 0"][..],
                "truncating_remainder(n, d) <= 0",
            ),
        ] {
            let requires = requirements
                .iter()
                .map(|r| format!("requires {r}; "))
                .collect::<String>();
            let source = format!(
                "theorem law(n: Integer, d: Integer) {{ {requires}ensures {goal} by {{ apply({name}(n, d)); }} }}"
            );
            verify_c0_sources(&source, &[]).unwrap();
            let expanded = expand_c0_claim_source_by_label(&source, &[], "law.ensures_0").unwrap();
            verify_c0_sources(&expanded, &[]).unwrap();
            for guard in requirements {
                let invalid = source.replace(&format!("requires {guard};"), "");
                assert!(verify_c0_sources(&invalid, &[]).is_err(), "{invalid}");
            }
            let invalid = source.replace(&format!("ensures {goal}"), "ensures n == d");
            assert!(verify_c0_sources(&invalid, &[]).is_err(), "{invalid}");
        }
    }

    #[test]
    #[ignore = "nightly: 0.8s in the parallel gate"]
    fn integer_truncation_applications_scale_with_steps_and_unused_bounds() {
        let goal = "n == truncating_quotient(n, d) * d + truncating_remainder(n, d)";
        let mut samples = Vec::new();
        for size in [4usize, 16, 64, 256] {
            let mut source =
                String::from("theorem law(n: Integer, d: Integer, z: Integer) { requires d != 0; ");
            for i in 0..size {
                source.push_str(&format!("requires z <= {i}; "));
            }
            source.push_str(&format!("ensures {goal} by {{ "));
            for _ in 0..size {
                source.push_str(&format!("have {goal} by {{ apply(integer_truncation_identity(n, d)) using {{ d != 0; }} }} "));
            }
            source.push_str("assumption(); } }");
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&source, &[])
            });
            result.unwrap_or_else(|error| panic!("{size}: {}", error.message()));
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(pair[1] <= pair[0] * 6, "{samples:?}");
        }
    }

    #[test]
    #[ignore = "nightly: 1.0s in the parallel gate"]
    fn multiply_order_and_fee_bounds_expand_and_reject_missing_evidence() {
        let fixture = include_str!("../../mdtests/integer_multiply_order.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        verify_c0_sources(source, &[]).unwrap();
        for label in [
            "checked_integer_multiply_order_nonnegative.ensures_0",
            "checked_integer_multiply_order_nonpositive.ensures_0",
            "checked_integer_scaled_product_bounds.ensures_0",
            "checked_integer_scaled_product_bounds.ensures_1",
            "fee_caller_division_bounds.ensures_0",
            "fee_caller_division_bounds.ensures_1",
            "fee_caller_division_bounds.ensures_2",
            "fee_caller_division_bounds.ensures_3",
        ] {
            let expanded = expand_c0_claim_source_by_label(source, &[], label).unwrap();
            verify_c0_sources(&expanded, &[]).unwrap();
        }
        let guarded = "theorem use_order(a: Integer, b: Integer, c: Integer) { requires a <= b; requires 0 <= c; ensures a * c <= b * c by { apply(integer_multiply_order_nonnegative(a,b,c)); } }";
        verify_c0_sources(guarded, &[]).unwrap();
        for bad in [
            guarded.replace("requires a <= b;", ""),
            guarded.replace("requires 0 <= c;", ""),
            guarded.replace("requires 0 <= c;", "requires c <= 0;"),
            guarded.replace("ensures a * c <= b * c", "ensures b * c <= a * c"),
        ] {
            assert!(verify_c0_sources(&bad, &[]).is_err(), "{bad}");
        }
        for requirement in [
            "requires -9223372036854775808 <= fee;",
            "requires fee <= 9223372036854775807;",
            "requires 0 <= at_size;",
            "requires at_size <= size;",
        ] {
            assert!(
                verify_c0_sources(&source.replace(requirement, ""), &[]).is_err(),
                "{requirement}"
            );
        }
    }

    #[test]
    #[ignore = "nightly: 0.7s in the parallel gate"]
    fn multiply_order_applications_scale_with_explicit_inputs() {
        let mut samples = Vec::new();
        for size in [4usize, 16, 64, 256] {
            let mut source = String::from(
                "theorem order(a: Integer,b: Integer,c: Integer,z: Integer) { requires a <= b; requires 0 <= c; ",
            );
            for i in 0..size {
                source.push_str(&format!("requires z <= {i}; "));
            }
            source.push_str("ensures a * c <= b * c by { ");
            for _ in 0..size {
                source.push_str("have a * c <= b * c by { apply(integer_multiply_order_nonnegative(a,b,c)) using { a <= b; 0 <= c; } } ");
            }
            source.push_str("assumption(); } }");
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&source, &[])
            });
            result.unwrap();
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(pair[1] <= pair[0] * 6, "{samples:?}");
        }
    }

    #[test]
    fn scaled_quotient_derivations_expand_reverify_and_preserve_guards() {
        let fixture = include_str!("../../mdtests/integer_quotient_bound.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        verify_c0_sources(source, &[]).unwrap();
        for label in [
            "checked_quotient_lower.ensures_0",
            "checked_quotient_upper.ensures_0",
            "use_scaled_quotient.ensures_0",
            "use_scaled_quotient.ensures_1",
        ] {
            let expanded = expand_c0_claim_source_by_label(source, &[], label).unwrap();
            verify_c0_sources(&expanded, &[]).unwrap();
        }
        let guarded = "theorem lower(x: int64, d: Integer) { requires defined(x + 1i64); requires d != 0; requires 1 <= d; requires -100 * d <= to_integer(x) + 1; ensures -100 <= truncating_quotient(to_integer(x + 1i64), d) by { apply(int64_add_to_integer(x, 1i64)); have -100 * d <= to_integer(x + 1i64) by { rewrite(to_integer(x + 1i64) == to_integer(x) + 1); assumption(); } apply(integer_positive_divisor_quotient_lower(to_integer(x + 1i64), d, -100)); } }";
        verify_c0_sources(guarded, &[]).unwrap();
        for bad in [
            guarded.replace("requires defined(x + 1i64);", ""),
            guarded.replace("requires d != 0;", ""),
            guarded.replace("to_integer(x + 1i64)", "x + 1i64"),
        ] {
            assert!(verify_c0_sources(&bad, &[]).is_err(), "{bad}");
        }
    }
    #[test]
    fn negated_integer_order_arithmetic_expands_and_reverifies() {
        let fixture = include_str!("../../mdtests/integer_negated_order_arithmetic.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        verify_c0_sources(source, &[]).unwrap();
        for label in ["negated_lower.ensures_0", "negated_upper.ensures_0"] {
            let expanded = expand_c0_claim_source_by_label(source, &[], label).unwrap();
            verify_c0_sources(&expanded, &[]).unwrap();
        }
        for bad in [
            source.replace("requires not (n <= 0);", "requires n <= 0;"),
            source.replace("requires not (0 <= n);", "requires 0 <= n;"),
        ] {
            assert!(verify_c0_sources(&bad, &[]).is_err());
        }
    }

    #[test]
    #[ignore = "nightly: 1.7s in the parallel gate"]
    fn strict_scaled_quotient_bounds_expand_and_reject_missing_guards() {
        let fixture = include_str!("../../mdtests/integer_quotient_strict_bound.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        verify_c0_sources(source, &[]).unwrap();
        for label in [
            "checked_strict_lower.ensures_0",
            "checked_strict_upper.ensures_0",
            "use_strict_lower.ensures_0",
            "use_strict_upper.ensures_0",
            "fee_floor_quotient_fit.ensures_0",
            "fee_floor_quotient_fit.ensures_1",
            "fee_ceiling_quotient_fit.ensures_0",
            "fee_ceiling_quotient_fit.ensures_1",
        ] {
            let expanded = expand_c0_claim_source_by_label(source, &[], label).unwrap();
            verify_c0_sources(&expanded, &[]).unwrap();
        }
        let uses = source.split("theorem use_strict_lower").nth(1).unwrap();
        let uses = format!("theorem use_strict_lower{uses}");
        for guard in [
            "requires d != 0;",
            "requires 1 <= d;",
            "requires bound < 0;",
            "requires 0 < bound;",
            "requires bound * d < n;",
            "requires n < bound * d;",
        ] {
            let bad = uses.replace(guard, "");
            assert!(verify_c0_sources(&bad, &[]).is_err(), "missing {guard}");
        }
        for (from, to) in [
            ("bound * d < n", "bound * d <= n"),
            ("n < bound * d", "n <= bound * d"),
            ("bound < 0", "bound <= 0"),
            ("0 < bound", "0 <= bound"),
        ] {
            let bad = uses.replacen(&format!("requires {from};"), &format!("requires {to};"), 1);
            assert!(verify_c0_sources(&bad, &[]).is_err(), "weakened {from}");
        }
    }

    #[test]
    #[ignore = "nightly: 0.8s in the parallel gate"]
    fn scaled_quotient_applications_scale_with_steps_and_unused_bounds() {
        let mut samples = Vec::new();
        for size in [4usize, 16, 64, 256] {
            let mut source = String::from(
                "theorem lower(n: Integer, d: Integer, b: Integer, z: Integer) { requires d != 0; requires 1 <= d; requires b * d <= n; ",
            );
            for i in 0..size {
                source.push_str(&format!("requires z <= {i}; "));
            }
            source.push_str("ensures b <= truncating_quotient(n, d) by { ");
            for _ in 0..size {
                source.push_str("have b <= truncating_quotient(n, d) by { apply(integer_positive_divisor_quotient_lower(n, d, b)) using { d != 0; 1 <= d; b * d <= n; } } ");
            }
            source.push_str("assumption(); } }");
            let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&source, &[])
            });
            checked.unwrap_or_else(|error| panic!("{size}: {}", error.message()));
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(pair[1] <= pair[0] * 6, "{samples:?}");
        }
    }

    #[test]
    fn correction_endpoint_lemmas_expand_and_reject_missing_evidence() {
        let fixture = include_str!("../../mdtests/integer_correction_endpoint_bounds.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        verify_c0_sources(source, &[]).unwrap();
        for label in [
            "derived_lower_correction_bound.ensures_0",
            "derived_upper_correction_bound.ensures_0",
            "use_lower_correction_bound.ensures_0",
            "use_upper_correction_bound.ensures_0",
        ] {
            let expanded = expand_c0_claim_source_by_label(source, &[], label).unwrap();
            verify_c0_sources(&expanded, &[]).unwrap();
        }
        for (which, bound, scaled, sign, goal) in [
            (
                "lower",
                "bound <= q",
                "bound * d <= n",
                "r < 0",
                "bound + 1 <= q",
            ),
            (
                "upper",
                "q <= bound",
                "n <= bound * d",
                "0 < r",
                "q <= bound + -1",
            ),
        ] {
            let premises = [bound, scaled, "n == q * d + r", sign];
            let source = format!(
                "theorem correction(n: Integer, d: Integer, q: Integer, r: Integer, bound: Integer) {{ {} ensures {goal} by {{ apply(integer_{which}_correction_bound(n, d, q, r, bound)); }} }}",
                premises
                    .iter()
                    .map(|p| format!("requires {p}; "))
                    .collect::<String>()
            );
            verify_c0_sources(&source, &[]).unwrap();
            for premise in premises {
                let bad = source.replace(&format!("requires {premise};"), "");
                assert!(verify_c0_sources(&bad, &[]).is_err(), "{bad}");
            }
            for bad in [
                source.replace(&format!("requires {sign};"), "requires r == 0;"),
                source.replace("n == q * d + r", "n == q * d + -r"),
            ] {
                assert!(verify_c0_sources(&bad, &[]).is_err(), "{bad}");
            }
        }
    }

    #[test]
    #[ignore = "nightly: 1.0s in the parallel gate"]
    fn correction_endpoint_applications_scale_with_steps_and_unused_bounds() {
        let mut samples = Vec::new();
        for size in [4usize, 16, 64, 256] {
            let mut source = String::from(
                "theorem correction(n: Integer, d: Integer, q: Integer, r: Integer, b: Integer, z: Integer) { requires b <= q; requires b * d <= n; requires n == q * d + r; requires r < 0; ",
            );
            for i in 0..size {
                source.push_str(&format!("requires z <= {i}; "));
            }
            source.push_str("ensures b + 1 <= q by { ");
            for _ in 0..size {
                source.push_str("have b + 1 <= q by { apply(integer_lower_correction_bound(n, d, q, r, b)) using { b <= q; b * d <= n; n == q * d + r; r < 0; } } ");
            }
            source.push_str("assumption(); } }");
            let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&source, &[])
            });
            checked.unwrap_or_else(|error| panic!("{size}: {}", error.message()));
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(pair[1] <= pair[0] * 6, "{samples:?}");
        }
    }

    #[test]
    fn normalized_opposite_bounds_print_and_reverify_equality_certificates() {
        for (bounds, goal) in [
            ("requires b <= x; requires not (b + 1 <= x);", "x == b"),
            ("requires x <= b; requires not (x <= b + -1);", "x == b"),
            ("requires b <= x; requires x < b + 1;", "x == b"),
        ] {
            let source = format!(
                "theorem pinned(x: Integer, b: Integer) {{ {bounds} ensures {goal} by {{ arithmetic() using {{ {}; }} }} }}",
                bounds.replace("requires ", "").trim_end_matches(';')
            );
            verify_c0_sources(&source, &[]).unwrap_or_else(|error| panic!("{}", error.message()));
            let expanded =
                expand_c0_claim_source_by_label(&source, &[], "pinned.ensures_0").unwrap();
            assert!(expanded.contains("equal_from_bounds"), "{expanded}");
            verify_c0_sources(&expanded, &[]).unwrap();
            assert!(
                verify_c0_sources(&source.replace("ensures x == b", "ensures x == b + 1"), &[])
                    .is_err()
            );
            assert!(
                verify_c0_sources(&expanded.replace("=> x == b;", "=> x == b + 1;"), &[]).is_err()
            );
        }
    }

    #[test]
    fn signed_int64_minimum_literal_preserves_type_and_round_trips() {
        let source = "theorem minimum() { ensures to_integer(-9223372036854775808i64) == -9223372036854775808 by { normalize(); } }";
        verify_c0_sources(source, &[]).unwrap();
        let expanded = expand_c0_claim_source_by_label(source, &[], "minimum.ensures_0").unwrap();
        verify_c0_sources(&expanded, &[]).unwrap();
        for literal in [
            "9223372036854775808i64",
            "-9223372036854775809i64",
            "9223372036854775809i64",
        ] {
            assert!(
                verify_c0_sources(&source.replace("-9223372036854775808i64", literal), &[])
                    .is_err(),
                "{literal}"
            );
        }
        assert!(
            verify_c0_sources(
                "theorem bad() { ensures defined(0i64 - 9223372036854775808i64) by { normalize(); } }",
                &[]
            )
            .is_err()
        );
        assert!(
            verify_c0_sources(
                "theorem bad() { ensures defined(-(-9223372036854775808i64)) by { normalize(); } }",
                &[]
            )
            .is_err()
        );
    }

    #[test]
    fn fee_correction_endpoint_oracle_checks_both_modes_and_overflow_neighbors() {
        let lower = i128::from(i64::MIN);
        let upper = i128::from(i64::MAX);
        for d in [1i128, 2, 3, 17, i128::from(i32::MAX)] {
            for q in [lower, lower + 1, -2, -1, 0, 1, 2, upper - 1, upper] {
                for offset in [1 - d, -1, 0, 1, d - 1] {
                    let n = q * d + offset;
                    if !(lower * d <= n && n <= upper * d) {
                        continue;
                    }
                    for round_down in [false, true] {
                        let quotient = i64::try_from(n / d).unwrap();
                        let r = n % d;
                        let correction = i64::from(r > 0) - i64::from(r != 0 && round_down);
                        let actual = i128::from(quotient.checked_add(correction).unwrap());
                        let expected = if round_down {
                            n.div_euclid(d)
                        } else {
                            -(-n).div_euclid(d)
                        };
                        assert_eq!(actual, expected, "{n}/{d}, down={round_down}");
                    }
                }
            }
            if d > 1 {
                let above = upper * d + 1;
                let below = lower * d - 1;
                assert!(i64::try_from(above / d).unwrap().checked_add(1).is_none());
                assert!(i64::try_from(below / d).unwrap().checked_add(-1).is_none());
            }
        }
    }

    #[test]
    #[ignore = "nightly: 0.7s in the parallel gate"]
    fn normalized_opposite_bound_certificates_scale_with_steps_and_unused_facts() {
        let mut samples = Vec::new();
        for size in [4usize, 16, 64, 256] {
            let mut source = String::from(
                "theorem pinned(x: Integer, b: Integer, z: Integer) { requires b <= x; requires not (b + 1 <= x); ",
            );
            for i in 0..size {
                source.push_str(&format!("requires z <= {i}; "));
            }
            source.push_str("ensures x == b by { ");
            for _ in 0..size {
                source.push_str(
                    "have x == b by { arithmetic() using { b <= x; not (b + 1 <= x); } } ",
                );
            }
            source.push_str("assumption(); } }");
            let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&source, &[])
            });
            checked.unwrap_or_else(|error| panic!("{size}: {}", error.message()));
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(pair[1] <= pair[0] * 6, "{samples:?}");
        }
    }
}
