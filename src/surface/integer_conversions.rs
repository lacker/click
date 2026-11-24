//! Public spelling and source types of explicit Integer conversions.
use super::*;

pub(super) fn integer_conversion_target(name: &str) -> Option<InterfaceType> {
    Some(match name {
        "to_int8" => InterfaceType::Int8,
        "to_int16" => InterfaceType::Int16,
        "to_int32" => InterfaceType::Int32,
        "to_uint8" => InterfaceType::UInt8,
        "to_uint16" => InterfaceType::UInt16,
        "to_uint32" => InterfaceType::UInt32,
        "to_int64" => InterfaceType::Int64(LongRank::Long),
        "to_uint64" => InterfaceType::UInt64(LongRank::Long),
        "to_int128" => InterfaceType::Int128,
        "to_uint128" => InterfaceType::UInt128,
        _ => return None,
    })
}

pub(super) fn is_integer_conversion(name: &str) -> bool {
    name == "to_integer" || integer_conversion_target(name).is_some()
}

pub(super) fn machine_integer_source_type(interface_type: InterfaceType) -> bool {
    matches!(
        interface_type,
        InterfaceType::Int8
            | InterfaceType::Int16
            | InterfaceType::Int32
            | InterfaceType::UInt8
            | InterfaceType::UInt16
            | InterfaceType::UInt32
            | InterfaceType::Int64(_)
            | InterfaceType::UInt64(_)
            | InterfaceType::Int128
            | InterfaceType::UInt128
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

    fn library_declarations(source: &str, names: &[&str]) -> String {
        let mut result = String::new();
        for name in names {
            let start = source.find(&format!("theorem {name}(")).unwrap();
            let body = start + source[start..].find('{').unwrap();
            let mut depth = 1;
            let mut end = body + 1;
            while depth != 0 {
                match source.as_bytes()[end] {
                    b'{' => depth += 1,
                    b'}' => depth -= 1,
                    _ => {}
                }
                end += 1;
            }
            result.push_str(&source[start..end]);
            result.push('\n');
        }
        result
    }

    #[test]
    fn integer_order_axioms_apply_without_certificates_or_search() {
        let source = r#"
import click::integer;
theorem sum(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a <= b;
    requires c <= d;
    ensures a + c <= b + d by {
        apply(integer::add_le(a, b, c, d));
    }
}
theorem scaled(x: Integer, y: Integer, k: Integer) {
    requires x <= y;
    requires 0 <= k;
    ensures x * k <= y * k by {
        apply(integer::multiply_order_nonnegative(x, y, k));
    }
}
theorem rounded(x: Integer) {
    requires x * 2 <= 5;
    ensures x <= 2 by {
        have (2 * 2) + 1 == 5 by { normalize(); }
        have x * 2 <= (2 * 2) + 1 by {
            rewrite((2 * 2) + 1, 5);
            close();
        }
        apply(integer::round_down_le(x, 2, 2, 1));
    }
}
theorem refuted(a: Integer, b: Integer, c: Integer, d: Integer) {
    requires a <= b;
    requires c <= d;
    requires not (a + c <= b + d);
    ensures false by {
        have a + c <= b + d by {
            apply(integer::add_le(a, b, c, d));
        }
        contradiction(a + c <= b + d);
    }
}
"#;
        crate::surface::proof::without_implicit_solve(|| verify_c_sources(source, &[])).unwrap();
        let expanded = expand_c_claim_source_by_label(source, &[], "rounded.ensures_0").unwrap();
        crate::surface::proof::without_implicit_solve(|| verify_c_sources(&expanded, &[])).unwrap();
    }

    #[test]
    fn divisor_sign_identities_require_their_explicit_nonzero_guard() {
        for (name, goal) in [
            (
                "quotient_negate_divisor",
                "truncating_quotient(n, d) == -truncating_quotient(n, -d)",
            ),
            (
                "remainder_negate_divisor",
                "truncating_remainder(n, d) == truncating_remainder(n, -d)",
            ),
        ] {
            let source = format!(
                "import click::integer; theorem sign(n: Integer, d: Integer) {{ requires d != 0; requires -d != 0;
                ensures {goal} by {{ apply(integer::{name}(n, d)); }} }}"
            );
            crate::surface::proof::without_implicit_solve(|| verify_c_sources(&source, &[]))
                .unwrap();
            assert!(
                verify_c_sources(
                    &source.replace("requires d != 0; requires -d != 0;", ""),
                    &[]
                )
                .is_err()
            );
            assert!(verify_c_sources(&source.replace(goal, "false"), &[]).is_err());
        }
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: signed quotient/remainder interval expansion and replay"]
    fn division_intervals_expand_without_normalization() {
        let lib = include_str!("../../library/integer.click");
        let local = &lib[lib
            .find("// Ordinary proofs for explicit quotient")
            .unwrap()
            ..lib.find("theorem quotient_negate_divisor(").unwrap()];
        // The two bare divisor-sign declarations have independent kernel/oracle
        // checks. Every derived interval helper must replay without search.
        let mut foundation = String::new();
        for name in [
            "positive_divisor_quotient_lower",
            "positive_divisor_quotient_upper",
            "step_le_lt",
            "le_substitute",
            "equal_substitute",
            "equal_add",
            "equal_multiply",
            "add_right_order",
            "subtract_right_order",
            "subtract_left_order",
            "negate_multiply",
            "equal_negate",
            "sum_commute",
            "sum_difference",
        ] {
            let start = lib.find(&format!("theorem {name}(")).unwrap();
            let body = start + lib[start..].find('{').unwrap();
            let mut depth = 1;
            let mut end = body + 1;
            while depth != 0 {
                match lib.as_bytes()[end] {
                    b'{' => depth += 1,
                    b'}' => depth -= 1,
                    _ => {}
                }
                end += 1;
            }
            foundation.push_str(&lib[start..end]);
            foundation.push('\n');
        }
        crate::surface::proof::without_implicit_solve(|| {
            verify_c_sources(
                &format!("import click::integer;\n{foundation}\n{local}"),
                &[],
            )
        })
        .unwrap();
        for (ln, un, ld, ud) in [
            (-8i64, 9, 2, 5),
            (-8, 9, -5, -2),
            (2, 3, 5, 8),
            (-3, -2, -8, -5),
            (2, 9, 1, 3),
            (-9, -2, 1, 4),
        ] {
            for remainder in [false, true] {
                let mut values = Vec::new();
                for n in ln..=un {
                    for d in ld..=ud {
                        values.push(if remainder { n % d } else { n / d });
                    }
                }
                let (min, max) = (*values.iter().min().unwrap(), *values.iter().max().unwrap());
                // The legacy interval envelope can be weaker than enumeration
                // for remainders. Choose its own valid envelope, not a tighter
                // completeness claim for the search strategy.
                let (min, max) = if remainder && ln.abs().max(un.abs()) >= ld.abs().min(ud.abs()) {
                    let m = ld.abs().max(ud.abs()) - 1;
                    (
                        if ln < 0 { -(-ln).min(m) } else { 0 },
                        if un > 0 { un.min(m) } else { 0 },
                    )
                } else {
                    (min, max)
                };
                for (lower, bound) in [(true, min), (false, max)] {
                    let op = if remainder {
                        "truncating_remainder"
                    } else {
                        "truncating_quotient"
                    };
                    let goal = if lower {
                        format!("{bound} <= value")
                    } else {
                        format!("value <= {bound}")
                    };
                    let source=format!("theorem interval(n: Integer, d: Integer) {{
                        requires {ln} <= n; requires n <= {un}; requires {ld} <= d; requires d <= {ud}; requires d != 0;
                        let value: Integer = {op}(n, d);
                        ensures {goal} by {{ close() using {{ {ln} <= n; n <= {un}; {ld} <= d; d <= {ud}; }}; }}
                    }}");
                    verify_c_sources(&source, &[])
                        .unwrap_or_else(|error| panic!("{source}\n{}", error.message()));
                    let expanded =
                        expand_c_claim_source_by_label(&source, &[], "interval.ensures_0").unwrap();
                    assert!(!expanded.contains("normalize("), "{expanded}");
                    crate::surface::proof::without_implicit_solve(|| {
                        verify_c_sources(&expanded, &[])
                    })
                    .unwrap();
                }
            }
        }
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: multiply-order sign/orientation expansion and replay"]
    fn multiplication_order_expands_without_normalization() {
        for (sign, goals) in [
            (
                "0 <= k",
                ["a * k <= b * k", "k * a <= k * b", "k * a <= b * k"],
            ),
            (
                "k <= 0",
                ["b * k <= a * k", "k * b <= k * a", "k * b <= a * k"],
            ),
        ] {
            for goal in goals {
                let source = format!(
                    "theorem order(a: Integer, b: Integer, k: Integer) {{
                    requires a <= b; requires {sign};
                    ensures {goal} by {{ close() using {{ a <= b; {sign}; }}; }}
                }}"
                );
                verify_c_sources(&source, &[]).unwrap();
                let expanded =
                    expand_c_claim_source_by_label(&source, &[], "order.ensures_0").unwrap();
                assert!(!expanded.contains("normalize("), "{expanded}");
                assert!(expanded.contains("::multiply_order_non"), "{expanded}");
                crate::surface::proof::without_implicit_solve(|| verify_c_sources(&expanded, &[]))
                    .unwrap();
                for selected in ["a <= b;", &format!("{sign};")] {
                    let mut omitted = source.clone();
                    let i = omitted.rfind(selected).unwrap();
                    omitted.replace_range(i..i + selected.len(), "");
                    assert!(verify_c_sources(&omitted, &[]).is_err());
                }
            }
        }
        let lib = include_str!("../../library/integer.click");
        let source = &lib[lib.find("theorem scaled_product_bounds(").unwrap()
            ..lib.find("theorem product_lower_bound(").unwrap()];
        crate::surface::proof::without_implicit_solve(|| {
            verify_c_sources(&format!("import click::integer;\n{source}"), &[])
        })
        .unwrap();
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: expansion and replay across interval sign quadrants"]
    fn product_bounds_expand_to_explicit_library_applications() {
        check_product_bound_refusals();
        let library = include_str!("../../library/integer.click");
        let ordinary = format!(
            "import click::integer;\n{}",
            library_declarations(
                library,
                &[
                    "negate_order",
                    "le_transitive",
                    "lt_le",
                    "multiply_order_nonpositive",
                    "product_lower_bound",
                    "product_upper_bound"
                ]
            )
        );
        crate::surface::proof::without_implicit_solve(|| verify_c_sources(&ordinary, &[])).unwrap();
        for (lo_x, hi_x, lo_y, hi_y) in [
            (2, 3, 4, 5),
            (-3, -2, 4, 5),
            (2, 3, -5, -4),
            (-3, -2, -5, -4),
            (-2, 3, -4, 5),
            (0, 0, -4, 5),
        ] {
            let corners = [lo_x * lo_y, lo_x * hi_y, hi_x * lo_y, hi_x * hi_y];
            for (lower, target) in [
                (true, *corners.iter().min().unwrap()),
                (false, *corners.iter().max().unwrap()),
                (true, *corners.iter().min().unwrap() - 1),
                (false, *corners.iter().max().unwrap() + 1),
            ] {
                let product = if lo_x < 0 { "named_product" } else { "x * y" };
                let goal = if lower {
                    format!("{target} <= {product}")
                } else {
                    format!("{product} <= {target}")
                };
                let binding = if lo_x < 0 {
                    "let named_product: Integer = x * y;"
                } else {
                    ""
                };
                let premises = format!("{lo_x} <= x; x <= {hi_x}; {lo_y} <= y; y <= {hi_y};");
                let source = format!(
                    "theorem bound(x: Integer, y: Integer) {{
                    requires {lo_x} <= x; requires x <= {hi_x};
                    requires {lo_y} <= y; requires y <= {hi_y};
                    {binding}
                    ensures {goal} by {{ close() using {{ {premises} }}; }}
                }}"
                );
                verify_c_sources(&source, &[]).unwrap();
                let expanded =
                    expand_c_claim_source_by_label(&source, &[], "bound.ensures_0").unwrap();
                assert!(
                    expanded.contains(if lower {
                        "::product_lower_bound("
                    } else {
                        "::product_upper_bound("
                    }),
                    "{expanded}"
                );
                assert!(!expanded.contains("normalize("), "{expanded}");
                crate::surface::proof::without_implicit_solve(|| verify_c_sources(&expanded, &[]))
                    .unwrap();
            }
        }
    }

    fn check_product_bound_refusals() {
        let source = "theorem bound(x: Integer, y: Integer) {
            requires -2 <= x; requires x <= 3; requires -4 <= y; requires y <= 5;
            ensures x * y <= 15 by {
                close() using { -2 <= x; x <= 3; -4 <= y; y <= 5; };
            }
        }";
        verify_c_sources(source, &[]).unwrap();
        for premise in ["-2 <= x;", "x <= 3;", "-4 <= y;", "y <= 5;"] {
            // Keep the omitted premise in the ambient context. Restricted
            // solve must use only its remaining selected intervals.
            let selected = source.rfind(premise).unwrap();
            let mut omitted = source.to_owned();
            omitted.replace_range(selected..selected + premise.len(), "");
            assert!(verify_c_sources(&omitted, &[]).is_err(), "{premise}");
        }
        assert!(verify_c_sources(&source.replace("<= 15 by", "<= 14 by"), &[]).is_err());
    }

    #[test]
    fn integer_order_axioms_refuse_missing_guards_and_unrelated_conclusions() {
        for (name, parameters, arguments, premises, goal) in [
            (
                "add_le",
                "a: Integer, b: Integer, c: Integer, d: Integer",
                "a, b, c, d",
                vec!["a <= b", "c <= d"],
                "a + c <= b + d",
            ),
            (
                "multiply_order_nonnegative",
                "a: Integer, b: Integer, k: Integer",
                "a, b, k",
                vec!["a <= b", "0 <= k"],
                "a * k <= b * k",
            ),
            (
                "round_down_le",
                "x: Integer, b: Integer, d: Integer, r: Integer",
                "x, b, d, r",
                vec!["0 < d", "r < d", "x * d <= b * d + r"],
                "x <= b",
            ),
        ] {
            let source = |omitted: Option<usize>, goal: &str| {
                let requires = premises
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| Some(*index) != omitted)
                    .map(|(_, premise)| format!("requires {premise}; "))
                    .collect::<String>();
                format!(
                    "import click::integer; theorem test({parameters}) {{ {requires} ensures {goal} by {{ apply(integer::{name}({arguments})); }} }}"
                )
            };
            for index in 0..premises.len() {
                assert!(
                    verify_c_sources(&source(Some(index), goal), &[]).is_err(),
                    "{name}: guard {index}"
                );
            }
            assert!(
                verify_c_sources(&source(None, "false"), &[]).is_err(),
                "{name}: forged conclusion"
            );
        }
    }

    #[test]
    fn selected_integer_sum_expands_to_an_ordinary_law_application() {
        let source = "theorem sum(a: Integer, b: Integer, c: Integer, d: Integer) { requires a <= b; requires c <= d; ensures a + c <= b + d by { close() using { a <= b; c <= d; }; } }";
        let expanded = expand_c_claim_source_by_label(source, &[], "sum.ensures_0").unwrap();
        assert!(expanded.contains("integer::add_le"), "{expanded}");
        assert!(!expanded.contains("solve("), "{expanded}");
        crate::surface::proof::without_implicit_solve(|| verify_c_sources(&expanded, &[])).unwrap();
        // An ambient second bound cannot fill an explicitly omitted premise.
        assert!(
            verify_c_sources(&source.replace("a <= b; c <= d; };", "a <= b; };"), &[]).is_err()
        );
    }

    #[test]
    fn integer_order_axiom_declarations_match_an_independent_bigint_oracle() {
        use num_bigint::BigInt;
        fn expression(term: &ContractExpression, values: &BTreeMap<String, BigInt>) -> BigInt {
            match term {
                ContractExpression::Binding(name)
                | ContractExpression::ProgramExpression(ProgramExpression::Variable(
                    crate::kernel::BindingName::Named(name),
                )) => values[name].clone(),
                ContractExpression::IntegerLiteral(value) => value.parse().unwrap(),
                ContractExpression::Add(a, b) => expression(a, values) + expression(b, values),
                ContractExpression::Subtract(a, b) => expression(a, values) - expression(b, values),
                ContractExpression::Multiply(a, b) => expression(a, values) * expression(b, values),
                ContractExpression::Negate(a) => -expression(a, values),
                _ => panic!("unexpected order axiom expression: {term:?}"),
            }
        }
        fn proposition(p: &ClickProposition, values: &BTreeMap<String, BigInt>) -> bool {
            let ClickProposition::Comparison {
                left,
                operator,
                right,
            } = p
            else {
                panic!("unexpected order axiom proposition: {p:?}")
            };
            let (left, right) = (expression(left, values), expression(right, values));
            match operator {
                ComparisonOperator::LessEqual => left <= right,
                ComparisonOperator::LessThan => left < right,
                ComparisonOperator::Equal => left == right,
                _ => panic!("unexpected order axiom operator: {operator:?}"),
            }
        }
        let library = standard_library_theorem_definitions().unwrap();
        let large: BigInt = (BigInt::from(1) << 160) + 1;
        let mut samples: Vec<BigInt> = (-2..=2).map(BigInt::from).collect();
        samples.extend([large.clone(), -large]);
        for name in [
            "add_le",
            "multiply_order_nonnegative",
            "multiply_commutative",
            "multiply_negate",
            "multiply_add",
            "multiply_associative",
            "round_down_le",
            "le_antisymmetric",
            "lt_step_le",
        ] {
            let law = library
                .iter()
                .find(|law| law.name() == format!("click::integer::{name}"))
                .unwrap();
            assert!(law.is_axiom());
            let arity = law.parameters().len();
            let mut applicable = 0;
            for mut index in 0..samples.len().pow(arity as u32) {
                let values = law
                    .parameters()
                    .iter()
                    .map(|parameter| {
                        let value = samples[index % samples.len()].clone();
                        index /= samples.len();
                        (parameter.name().to_owned(), value)
                    })
                    .collect();
                if law.requires().iter().all(|requirement| {
                    let Requirement::Proposition(p) = requirement else {
                        panic!("resource premise in {name}")
                    };
                    proposition(p, &values)
                }) {
                    applicable += 1;
                    for ensure in law.ensures() {
                        let Ensure::Proposition(p) = ensure.ensure() else {
                            panic!("resource conclusion in {name}")
                        };
                        assert!(proposition(p, &values), "{name}: {values:?}");
                    }
                }
            }
            assert!(applicable > 0, "{name}: vacuous oracle");
        }
    }

    #[test]
    fn int32_remainder_bridge_requires_definedness_and_expands() {
        let source = "import click::integer; theorem remainder(a: int32, b: int32) { requires defined(a % b); requires to_integer(b) != 0; ensures to_integer(a % b) == truncating_remainder(to_integer(a), to_integer(b)) by { apply(integer::int32_remainder_to_integer(a, b)); } }";
        verify_c_sources(source, &[]).unwrap();
        let expanded = expand_c_claim_source_by_label(source, &[], "remainder.ensures_0").unwrap();
        verify_c_sources(&expanded, &[]).unwrap();
        assert!(verify_c_sources(&source.replace("requires defined(a % b);", ""), &[]).is_err());
        // `defined(a % b)` states `b != 0`, which is the one form of
        // `to_integer(b) != 0`, so the disequality alone is redundant.
        verify_c_sources(&source.replace("requires to_integer(b) != 0;", ""), &[]).unwrap();
        for (a, b) in [("0", "0"), ("-2147483648", "-1")] {
            let invalid = format!(
                "import click::integer; theorem invalid() {{ ensures to_integer({a} % {b}) == 0 by {{ apply(integer::int32_remainder_to_integer({a}, {b})); }} }}"
            );
            assert!(verify_c_sources(&invalid, &[]).is_err());
        }
        let forged = "theorem int32_remainder_to_integer(a: int32, b: int32) { requires b != 0; requires to_integer(b) != 0; ensures to_integer(a % b) == truncating_remainder(to_integer(a), to_integer(b)); }";
        assert!(verify_c_sources(forged, &[]).is_err());
    }

    #[test]
    fn uint32_product_bound_guard_expands_and_rejects_wrapped_or_signed_bounds() {
        let source = "import click::integer; theorem bounded(a: uint32, b: uint32) { requires to_integer(a) * to_integer(b) <= 4294967295; ensures b == 0u32 or a <= 4294967295u32 / b by { apply(integer::uint32_multiply_guard_by_integer_bound(a, b)); } }";
        verify_c_sources(source, &[]).unwrap();
        let expanded = expand_c_claim_source_by_label(source, &[], "bounded.ensures_0").unwrap();
        verify_c_sources(&expanded, &[]).unwrap();
        for requirement in [
            "to_integer(a * b) <= 4294967295",
            "to_integer(a as int32) * to_integer(b as int32) <= 4294967295",
            "to_integer(a) * to_integer(b) <= 4294967296",
        ] {
            let invalid =
                source.replace("to_integer(a) * to_integer(b) <= 4294967295", requirement);
            assert!(verify_c_sources(&invalid, &[]).is_err(), "{invalid}");
        }
        let missing = source.replace("requires to_integer(a) * to_integer(b) <= 4294967295;", "");
        assert!(verify_c_sources(&missing, &[]).is_err());
        let forged = "theorem uint32_multiply_guard_by_integer_bound(a: uint32, b: uint32) { requires to_integer(a) * to_integer(b) <= 4294967296; ensures b == 0u32 or a <= 4294967295u32 / b; }";
        assert!(verify_c_sources(forged, &[]).is_err());
    }

    #[test]
    fn scalar_casts_keep_byte_read_width_in_definedness() {
        let c = "int32 read(const uint8* p) { return (int32)p[0]; }";
        let source = "verifying \"read.c\"; int32 read(const uint8* p) { views p[0..1]; ensures defined(p[0] as int32); }";
        verify_c_sources(source, &[("read.c", c)]).unwrap();
        let expanded =
            expand_c_claim_source_by_label(source, &[("read.c", c)], "read.ensures_0").unwrap();
        verify_c_sources(&expanded, &[("read.c", c)]).unwrap();
        assert!(
            verify_c_sources(
                &source.replace(
                    "ensures defined(p[0] as int32)",
                    "ensures defined(p[1] as int32)"
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
                "spec enum Box {{ Wrapped(Integer) }} spec enum Outer {{ Wrapped(Box) }} theorem wrapped(x: int32) {{ ensures {value} == {value} by close(); }}"
            );
            assert!(verify_c_sources(&source, &[]).is_err(), "{source}");
            let bounded = source.replace("{ ensures", "{ requires defined(x + 1); ensures");
            verify_c_sources(&bounded, &[])
                .unwrap_or_else(|e| panic!("{}\n{bounded}", e.message()));
            let expanded =
                expand_c_claim_source_by_label(&bounded, &[], "wrapped.ensures_0").unwrap();
            verify_c_sources(&expanded, &[]).unwrap();
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
                "import click::integer; theorem round_trip(z: Integer) {{ requires z >= {lower}; requires z <= {upper}; ensures to_integer(to_{target}(z)) == z by {{ apply(integer::to_{target}_round_trip(z)); }} }}"
            );
            verify_c_sources(&source, &[]).unwrap_or_else(|e| panic!("{}\n{source}", e.message()));
            let expanded =
                expand_c_claim_source_by_label(&source, &[], "round_trip.ensures_0").unwrap();
            verify_c_sources(&expanded, &[]).unwrap();
            for missing in [
                format!("requires z >= {lower};"),
                format!("requires z <= {upper};"),
            ] {
                let invalid = source.replace(&missing, "");
                assert!(verify_c_sources(&invalid, &[]).is_err(), "{invalid}");
            }
        }
    }

    /// The omitted proof reads `to_integer(to_T(z))` as `z` under its range
    /// by `integer_cast_identity` at every format, 128 bits included, with
    /// no library law in scope; the expansion replays with no search. Each
    /// bound is needed, and a bound past the format's range is refused.
    #[test]
    fn solve_reads_an_integer_conversion_back_at_every_format() {
        for (target, lower, upper) in [
            ("int8", "-128", "127"),
            ("int64", "-9223372036854775808", "9223372036854775807"),
            ("uint128", "0", "340282366920938463463374607431768211455"),
        ] {
            let source = format!(
                "theorem round_trip(z: Integer) {{ requires z >= {lower}; requires z <= {upper}; ensures to_integer(to_{target}(z)) == z by {{ close(); }} }}"
            );
            verify_c_sources(&source, &[]).unwrap_or_else(|e| panic!("{}\n{source}", e.message()));
            let expanded =
                expand_c_claim_source_by_label(&source, &[], "round_trip.ensures_0").unwrap();
            assert!(!expanded.contains("integer_cast_identity"), "{expanded}");
            assert!(!expanded.contains("normalize("), "{expanded}");
            assert!(expanded.contains("close();"), "{expanded}");
            crate::surface::proof::without_implicit_solve(|| verify_c_sources(&expanded, &[]))
                .unwrap();
            for missing in [
                format!("requires z >= {lower};"),
                format!("requires z <= {upper};"),
            ] {
                let invalid = source.replace(&missing, "");
                assert!(verify_c_sources(&invalid, &[]).is_err(), "{invalid}");
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
                "theorem compose(x: int32) {{ ensures {expression} == {expression} by close(); }}"
            );
            assert!(verify_c_sources(&source, &[]).is_err(), "{source}");
            let bounded = source.replace("{ ensures", "{ requires defined(x + 1); ensures");
            verify_c_sources(&bounded, &[]).unwrap();
        }
    }

    #[test]
    fn forward_conversion_conditionals_preserve_the_argument_domain() {
        let expression = "if c == 0 { x + 1 } else { y + 1 }";
        let source = format!(
            "theorem branch(c: int32, x: int32, y: int32) {{ requires defined({expression}); ensures to_integer({expression}) == to_integer({expression}) by close(); }}"
        );
        verify_c_sources(&source, &[]).unwrap();
        let invalid = source.replace(&format!("requires defined({expression});"), "");
        assert!(verify_c_sources(&invalid, &[]).is_err());
        let one_branch = source.replace(
            &format!("requires defined({expression});"),
            "requires defined(x + 1);",
        );
        assert!(verify_c_sources(&one_branch, &[]).is_err());
    }

    #[test]
    fn forward_conversion_aliases_retain_definedness() {
        for alias in [
            "let a: Integer = to_integer(x + 1);",
            "let b: Integer = to_integer(x + 1); let a: Integer = b + 0;",
        ] {
            let source =
                format!("theorem alias(x: int32) {{ {alias} ensures a == a by close(); }}");
            assert!(verify_c_sources(&source, &[]).is_err(), "{source}");
            let bounded = source.replace("{ let", "{ requires defined(x + 1); let");
            verify_c_sources(&bounded, &[]).unwrap();
        }
    }

    #[test]
    fn forward_conversion_memory_requires_ownership_and_definedness() {
        let c = "int32 read(int32* p) { return *p; }";
        let source = "verifying \"read.c\"; int32 read(int32* p) { owns p[0..1]; requires defined(p[0] + 1); ensures to_integer(p[0] + 1) == to_integer(p[0] + 1); }";
        verify_c_sources(source, &[("read.c", c)]).unwrap();
        for missing in ["owns p[0..1];", "requires defined(p[0] + 1);"] {
            let invalid = source.replace(missing, "");
            assert!(
                verify_c_sources(&invalid, &[("read.c", c)]).is_err(),
                "{invalid}"
            );
        }
    }

    #[test]
    fn forward_conversion_keeps_intermediate_overflow_obligations() {
        // `defined((x + 1) + 1)` claims the outer addition; the inner one is
        // its own conjunct.
        let source = "theorem nested(x: int32) { requires defined(x + 1) and defined((x + 1) + 1); ensures to_integer((x + 1) + 1) == to_integer((x + 1) + 1) by close(); }";
        verify_c_sources(source, &[]).unwrap();
        let missing = source.replace(
            "requires defined(x + 1) and defined((x + 1) + 1);",
            "requires defined(x + 1);",
        );
        assert!(verify_c_sources(&missing, &[]).is_err());
        let cancelled = "theorem cancelled(x: int32) { ensures to_integer((x + 1) - 1) == to_integer((x + 1) - 1) by close(); }";
        assert!(verify_c_sources(cancelled, &[]).is_err());
        let bounded = cancelled.replace(
            "{ ensures",
            "{ requires defined(x + 1) and defined((x + 1) - 1); ensures",
        );
        verify_c_sources(&bounded, &[]).unwrap();
    }

    #[test]
    fn forward_conversion_requires_symbolic_argument_definedness() {
        for proof in ["normalize()", "close()"] {
            let source = format!(
                "theorem forward(x: int32) {{ ensures to_integer(x + 1) == to_integer(x + 1) by {{ {proof}; }} }}"
            );
            assert!(verify_c_sources(&source, &[]).is_err(), "{source}");
            let bounded = source.replace("{ ensures", "{ requires defined(x + 1); ensures");
            verify_c_sources(&bounded, &[])
                .unwrap_or_else(|error| panic!("{}\n{bounded}", error.message()));
            if proof == "close()" {
                let expanded =
                    expand_c_claim_source_by_label(&bounded, &[], "forward.ensures_0").unwrap();
                verify_c_sources(&expanded, &[]).unwrap();
            }
        }
        let c = "int32 identity(int32 x) { return x; }";
        let source = "verifying \"identity.c\"; int32 identity(int32 x) { ensures to_integer(x + 1) == to_integer(x + 1); }";
        assert!(verify_c_sources(source, &[("identity.c", c)]).is_err());
        let bounded = source.replace("{ ensures", "{ requires defined(x + 1); ensures");
        verify_c_sources(&bounded, &[("identity.c", c)]).unwrap();
    }

    #[test]
    fn integer_bounds_establish_c_add_definedness_without_circular_assumptions() {
        let source = "import click::integer; theorem safety(a: int32, b: int32) { requires to_integer(a) + to_integer(b) >= -2147483648; requires to_integer(a) + to_integer(b) <= 2147483647; ensures defined(a + b) by { apply(integer::int32_add_defined_by_integer_bounds(a, b)); } }";
        verify_c_sources(source, &[]).unwrap();
        let expanded = expand_c_claim_source_by_label(source, &[], "safety.ensures_0").unwrap();
        verify_c_sources(&expanded, &[]).unwrap();
        for missing in [
            "requires to_integer(a) + to_integer(b) >= -2147483648;",
            "requires to_integer(a) + to_integer(b) <= 2147483647;",
        ] {
            let invalid = source.replace(missing, "");
            assert!(verify_c_sources(&invalid, &[]).is_err(), "{invalid}");
        }
    }

    #[test]
    fn integer_machine_operation_laws_require_definedness() {
        for (name, operator) in [
            ("click::integer::int32_add_to_integer", "+"),
            ("click::integer::int32_subtract_to_integer", "-"),
        ] {
            let source = format!(
                "import click::integer; theorem bridge(a: int32, b: int32) {{ requires defined(a {operator} b); ensures to_integer(a {operator} b) == to_integer(a) {operator} to_integer(b) by {{ apply({name}(a, b)); }} }}"
            );
            verify_c_sources(&source, &[]).unwrap_or_else(|e| panic!("{}\n{source}", e.message()));
            let expanded =
                expand_c_claim_source_by_label(&source, &[], "bridge.ensures_0").unwrap();
            verify_c_sources(&expanded, &[]).unwrap();
            let invalid = source.replace(&format!("requires defined(a {operator} b);"), "");
            assert!(verify_c_sources(&invalid, &[]).is_err(), "{invalid}");
        }
    }

    #[test]
    fn uint32_small_remainder_expands_and_requires_strict_unsigned_evidence() {
        let source = "import click::integer; theorem lane(value: uint32, divisor: uint32) { requires value < divisor; ensures value % divisor == value by { apply(integer::uint32_less_than_divisor_implies_remainder_is_value(value, divisor)); } }";
        verify_c_sources(source, &[]).unwrap();
        let expanded = expand_c_claim_source_by_label(source, &[], "lane.ensures_0").unwrap();
        verify_c_sources(&expanded, &[]).unwrap();
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
            assert!(verify_c_sources(&invalid, &[]).is_err(), "{invalid}");
        }
    }

    #[test]
    fn uint32_remainder_bound_expands_and_requires_a_nonzero_divisor() {
        let source = "import click::integer; theorem bridge(value: uint32, divisor: uint32) { requires divisor != 0u32; ensures to_integer(value % divisor) < to_integer(divisor) by { apply(integer::uint32_remainder_less_than_divisor(value, divisor)); } }";
        verify_c_sources(source, &[]).unwrap();
        let expanded = expand_c_claim_source_by_label(source, &[], "bridge.ensures_0").unwrap();
        verify_c_sources(&expanded, &[]).unwrap();
        for invalid in [
            source.replace("requires divisor != 0u32;", ""),
            source.replace("requires divisor != 0u32;", "requires value != 0u32;"),
            source.replace("< to_integer(divisor) by", "< 65521 by"),
            source.replace("< to_integer(divisor) by", ">= to_integer(divisor) by"),
        ] {
            assert!(verify_c_sources(&invalid, &[]).is_err(), "{invalid}");
        }
    }

    #[test]
    fn uint32_integer_bounds_do_not_distribute_wrapping_or_define_zero_division() {
        for invalid in [
            "import click::integer; theorem wrong(value: uint32) { ensures to_integer(value) <= 2147483647 by { apply(integer::uint32_to_integer_bounds(value)); } }",
            "import click::integer; theorem wrong(value: uint32) { ensures to_integer(value + 1u32) == to_integer(value) + 1 by { apply(integer::uint32_to_integer_bounds(value + 1u32)); } }",
            "import click::integer; theorem wrong(value: uint32) { ensures to_integer(value / 0u32) == 0 by { apply(integer::uint32_to_integer_bounds(value / 0u32)); } }",
        ] {
            assert!(verify_c_sources(invalid, &[]).is_err(), "{invalid}");
        }
        // Specification division is total: the quotient by zero is an opaque
        // `uint32`, so it has the type's range and no other property.
        verify_c_sources(
            "import click::integer; theorem range(value: uint32) { ensures 0 <= to_integer(value / 0u32) by { apply(integer::uint32_to_integer_bounds(value / 0u32)); } }",
            &[],
        )
        .unwrap();
    }

    #[test]
    fn uint32_integer_order_bridges_recheck_expansion_and_require_evidence() {
        for (name, premise, conclusion) in [
            (
                "click::integer::uint32_less_equal_to_integer",
                "left <= right",
                "to_integer(left) <= to_integer(right)",
            ),
            (
                "click::integer::uint32_to_integer_less_equal_implies_less_equal",
                "to_integer(left) <= to_integer(right)",
                "left <= right",
            ),
            (
                "click::integer::uint32_to_integer_equal_implies_equal",
                "to_integer(left) == to_integer(right)",
                "left == right",
            ),
        ] {
            let source = format!(
                "import click::integer; theorem bridge(left: uint32, right: uint32) {{ requires {premise}; ensures {conclusion} by {{ apply({name}(left, right)); }} }}"
            );
            verify_c_sources(&source, &[]).unwrap();
            let expanded =
                expand_c_claim_source_by_label(&source, &[], "bridge.ensures_0").unwrap();
            verify_c_sources(&expanded, &[]).unwrap();
            let mut invalid = vec![
                source.replace(&format!("requires {premise};"), ""),
                source.replace("ensures", "ensures not"),
            ];
            // An equality's swapped instance states the same fact, so only
            // an order's swapped instance is wrong.
            if !conclusion.contains("==") {
                invalid.push(source.replace(
                    &format!("{name}(left, right)"),
                    &format!("{name}(right, left)"),
                ));
            }
            for invalid in invalid {
                assert!(verify_c_sources(&invalid, &[]).is_err(), "{invalid}");
            }
        }
    }

    #[test]
    fn integer_order_observation_requires_the_c_guard_and_rechecks_expansion() {
        let source = "import click::integer; theorem bridge(left: int32, right: int32) { requires left <= right; ensures to_integer(left) <= to_integer(right) by { apply(integer::int32_less_equal_to_integer(left, right)); } }";
        verify_c_sources(source, &[]).unwrap();
        let expanded = expand_c_claim_source_by_label(source, &[], "bridge.ensures_0").unwrap();
        verify_c_sources(&expanded, &[]).unwrap();

        for invalid in [
            source.replace("requires left <= right;", ""),
            source.replace("requires left <= right;", "requires right <= left;"),
        ] {
            assert!(
                verify_c_sources(&invalid, &[]).is_err(),
                "order observation accepted an invalid guard: {invalid}"
            );
        }
    }

    #[test]
    fn symbolic_integer_datatype_matches_are_exhaustive_and_checked() {
        let source = "spec enum Box<T> { Empty, Wrapped(T), }\n            function project(value: Box<Integer>) -> Integer { match value { Box::Empty => to_integer(0), Box::Wrapped(inner) => inner, } }\n\
            theorem symbolic(value: Box<Integer>) { ensures project(value) == project(value) by close(); }";
        verify_c_sources(source, &[]).unwrap();
        let expanded = expand_c_claim_source_by_label(source, &[], "symbolic.ensures_0").unwrap();
        verify_c_sources(&expanded, &[]).unwrap();
    }

    #[test]
    fn integer_datatype_match_reduces_known_constructor() {
        let source = r#"
            spec enum Box { Empty, Wrapped(Integer), }
            function project(value: Box) -> Integer { match value { Box::Empty => to_integer(0), Box::Wrapped(inner) => inner, } }
            theorem constructor_is_known() { ensures project(Box::Wrapped(to_integer(7))) == to_integer(7) by close(); }
        "#;
        verify_c_sources(source, &[]).unwrap();
        let expanded =
            expand_c_claim_source_by_label(source, &[], "constructor_is_known.ensures_0").unwrap();
        verify_c_sources(&expanded, &[]).unwrap();
    }

    #[test]
    fn deferred_integer_function_c_arguments_keep_mandatory_definedness() {
        let unguarded = "function f(x: int32) -> Integer { to_integer(x) }\n\
            theorem call(x: int32) { ensures f(x + 1) == f(x + 1) by close(); }";
        assert!(verify_c_sources(unguarded, &[]).is_err());

        let guarded = unguarded.replace("{ ensures", "{ requires defined(x + 1); ensures");
        verify_c_sources(&guarded, &[]).unwrap();
        let expanded = expand_c_claim_source_by_label(&guarded, &[], "call.ensures_0").unwrap();
        verify_c_sources(&expanded, &[]).unwrap();

        let mixed = "function mix(left: int32, right: int32) -> Integer { to_integer(left) }\n\
            theorem call(left: int32, right: int32) { requires defined(left + 1); requires defined(right + 1); ensures mix(left + 1, right + 1) == mix(left + 1, right + 1) by close(); }";
        verify_c_sources(mixed, &[]).unwrap();
        for missing in [
            "requires defined(left + 1); ",
            "requires defined(right + 1); ",
        ] {
            let invalid = mixed.replacen(missing, "", 1);
            assert!(verify_c_sources(&invalid, &[]).is_err(), "{invalid}");
        }
    }

    #[test]
    fn deferred_integer_function_argument_domains_cover_division_and_branches() {
        for proof in ["close()", "normalize()"] {
            let division = format!(
                "function f(x: int32) -> Integer {{ to_integer(x) }}\n\
                 theorem call(x: int32) {{ ensures f(-2147483648 / x) == f(-2147483648 / x) by {{ {proof}; }} }}"
            );
            // A zero divisor owes nothing; `MIN / -1` still overflows.
            assert!(verify_c_sources(&division, &[]).is_err(), "{division}");
            let guarded = division.replace("{ ensures", "{ requires x != -1; ensures");
            verify_c_sources(&guarded, &[]).unwrap();
            let expanded = expand_c_claim_source_by_label(&guarded, &[], "call.ensures_0").unwrap();
            verify_c_sources(&expanded, &[]).unwrap();

            let branch = format!(
                "function f(x: int32) -> Integer {{ to_integer(x) }}\n\
                 theorem call(c: int32, x: int32, y: int32) {{ ensures f(if c == 0 {{ x + 1 }} else {{ y + 1 }}) == f(if c == 0 {{ x + 1 }} else {{ y + 1 }}) by {{ {proof}; }} }}"
            );
            assert!(verify_c_sources(&branch, &[]).is_err(), "{branch}");
            let guarded = branch.replace(
                "{ ensures",
                "{ requires defined(if c == 0 { x + 1 } else { y + 1 }); ensures",
            );
            verify_c_sources(&guarded, &[]).unwrap();
            let expanded = expand_c_claim_source_by_label(&guarded, &[], "call.ensures_0").unwrap();
            verify_c_sources(&expanded, &[]).unwrap();
        }
    }

    #[test]
    fn deferred_integer_function_argument_domains_cross_algebraic_wrappers() {
        let source = "spec enum Box { Empty, Wrapped(int32), }\n\
            function pack(x: int32) -> Box { Box::Wrapped(x) }\n\
            function f(value: Box) -> Integer { 0 }\n\
            theorem call(x: int32) { ensures f(pack(x + 1)) == f(pack(x + 1)) by close(); }";
        assert!(verify_c_sources(source, &[]).is_err());
        let guarded = source.replace("{ ensures", "{ requires defined(x + 1); ensures");
        verify_c_sources(&guarded, &[]).unwrap();
        let expanded = expand_c_claim_source_by_label(&guarded, &[], "call.ensures_0").unwrap();
        verify_c_sources(&expanded, &[]).unwrap();
    }

    #[test]
    fn integer_conversion_proofs_expand_and_recheck() {
        for source in [
            "theorem conversion(x: int32) { ensures to_integer(x) == to_integer(x) by close(); }",
            "theorem conversion() { ensures to_integer(to_uint64(18446744073709551615)) == 18446744073709551615 by close(); }",
        ] {
            verify_c_sources(source, &[]).unwrap();
            let expanded =
                expand_c_claim_source_by_label(source, &[], "conversion.ensures_0").unwrap();
            verify_c_sources(&expanded, &[])
                .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
            assert!(!expanded.contains("by close()"), "{expanded}");
        }
    }

    #[test]
    fn wide_integer_observations_and_checked_conversions_expand_and_recheck() {
        for source in [
            "theorem observe(x: int128) { ensures to_integer(x) == to_integer(x) by close(); }",
            "theorem observe(x: uint128) { ensures to_integer(x) == to_integer(x) by close(); }",
            "theorem observe() { ensures to_integer(to_int128(-170141183460469231731687303715884105728)) == -170141183460469231731687303715884105728 by close(); }",
            "theorem observe() { ensures to_integer(to_int128(170141183460469231731687303715884105727)) == 170141183460469231731687303715884105727 by close(); }",
            "theorem observe() { ensures to_integer(to_uint128(340282366920938463463374607431768211455)) == 340282366920938463463374607431768211455 by close(); }",
        ] {
            verify_c_sources(source, &[])
                .unwrap_or_else(|error| panic!("{}\n{source}", error.message()));
            let expanded =
                expand_c_claim_source_by_label(source, &[], "observe.ensures_0").unwrap();
            verify_c_sources(&expanded, &[])
                .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
        }
        for (target, value) in [
            ("int128", "-170141183460469231731687303715884105729"),
            ("int128", "170141183460469231731687303715884105728"),
            ("uint128", "-1"),
            ("uint128", "340282366920938463463374607431768211456"),
        ] {
            let source = format!(
                "theorem bad() {{ ensures to_integer(to_{target}({value})) == {value} by close(); }}"
            );
            assert!(verify_c_sources(&source, &[]).is_err(), "{source}");
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
                    "theorem observe(z: Integer) {{ {requirements} ensures to_integer(to_{target}(z)) == to_integer(to_{target}(z)) by close(); }}"
                );
                assert_eq!(verify_c_sources(&source, &[]).is_ok(), valid, "{source}");
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
                    "theorem bad() {{ ensures to_{target}({value}) == to_{target}({value}) by close(); }}"
                );
                assert!(
                    verify_c_sources(&source, &[]).is_err(),
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
                "theorem conversion(z: Integer) {{ requires z >= {lower}; requires z <= {upper}; ensures to_{target}(z) == to_{target}(z) by close(); }}"
            );
            verify_c_sources(&source, &[]).unwrap_or_else(|error| {
                panic!(
                    "bounded symbolic conversion `{target}` rejected: {}",
                    error.message()
                )
            });
        }
    }

    #[test]
    fn to_integer_of_an_integer_is_that_integer() {
        let source = "theorem same(z: Integer) { ensures to_integer(z) == z by close(); }";
        verify_c_sources(source, &[]).unwrap();
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
                    "theorem conversion(z: Integer) {{{requires} ensures to_{target}(z) == to_{target}(z) by close(); }}"
                );
                assert!(
                    verify_c_sources(&source, &[]).is_err(),
                    "conversion `{target}` accepted without both bounds: {source}"
                );
            }
        }
    }

    #[test]
    fn wrapped_symbolic_conversions_keep_bounds_through_proofs_and_expansion() {
        let bounded = "theorem wrapped(z: Integer) { requires z >= -2147483648; requires z <= 2147483647; ensures to_int32(z) + 0 == to_int32(z) by close(); }";
        verify_c_sources(bounded, &[]).unwrap();
        let normalized = bounded.replace("by close(); }", "by { normalize(); } }");
        verify_c_sources(&normalized, &[]).unwrap();
        let expanded = expand_c_claim_source_by_label(bounded, &[], "wrapped.ensures_0").unwrap();
        verify_c_sources(&expanded, &[]).unwrap();

        for missing in ["requires z >= -2147483648;", "requires z <= 2147483647;"] {
            let invalid = bounded.replace(missing, "");
            assert!(verify_c_sources(&invalid, &[]).is_err(), "{invalid}");
        }

        let prior_have = "theorem prior(z: Integer) { requires z >= -2147483648; requires z <= 2147483647; let x: int32 = to_int32(z); ensures x + 0 == x by close(); }";
        verify_c_sources(prior_have, &[]).unwrap();
        let aliases = "theorem aliases(z: Integer) { requires z >= -2147483648; requires z <= 2147483647; let a: int32 = to_int32(z); let b: int32 = a + 0; ensures b == a by close(); }";
        verify_c_sources(aliases, &[]).unwrap();
        let no_bounds = "theorem aliases(z: Integer) { let a: int32 = to_int32(z); let b: int32 = a + 0; ensures b == a by close(); }";
        assert!(verify_c_sources(no_bounds, &[]).is_err());
    }

    #[test]
    fn integer_conversion_preserves_source_types_and_argument_definedness() {
        for (parameters, claim) in [
            ("", "to_integer(true) == 1"),
            ("", "to_integer() == 0"),
            ("", "to_integer(1, 2) == 1"),
            ("", "to_int32() == 0"),
            ("", "to_int32(1, 2) == 1"),
            ("x: int32", "to_int32(x) == x"),
            ("", "to_integer(-1) == to_integer(4294967295u32)"),
            (
                "",
                "to_integer(2147483647 + 1) == to_integer(2147483647 + 1)",
            ),
        ] {
            let source = format!("theorem bad({parameters}) {{ ensures {claim} by close(); }}");
            assert!(
                verify_c_sources(&source, &[]).is_err(),
                "invalid conversion accepted: {source}"
            );
        }
    }

    #[test]
    fn uint32_subtract_bridge_rechecks_guards_and_expansion() {
        let source = "import click::integer; theorem exact(left: uint32, right: uint32) { requires right <= left; ensures to_integer(left - right) == to_integer(left) - to_integer(right) by { apply(integer::uint32_subtract_to_integer(left, right)); } }";
        verify_c_sources(source, &[]).unwrap();
        let expanded = expand_c_claim_source_by_label(source, &[], "exact.ensures_0").unwrap();
        verify_c_sources(&expanded, &[]).unwrap();
        for invalid in [
            source.replace("requires right <= left;", ""),
            source.replace("requires right <= left;", "requires defined(left - right);"),
            source.replace("requires right <= left;", "requires left <= right;"),
            source.replace(
                "to_integer(left) - to_integer(right) by",
                "to_integer(left) + to_integer(right) by",
            ),
        ] {
            assert!(verify_c_sources(&invalid, &[]).is_err(), "{invalid}");
        }
        for (left, right, difference) in [
            (0u32, 0u32, 0u32),
            (65521, 65520, 1),
            (0x8000_0000, 1, 0x7fff_ffff),
            (u32::MAX, 0, u32::MAX),
            (u32::MAX, 0x8000_0000, 0x7fff_ffff),
        ] {
            let concrete = format!(
                "import click::integer; theorem boundary() {{ ensures to_integer({left}u32 - {right}u32) == {difference} by {{ apply(integer::uint32_subtract_to_integer({left}u32, {right}u32)); close(); }} }}"
            );
            verify_c_sources(&concrete, &[]).unwrap();
        }
        let underflow = "import click::integer; theorem wrapping() { ensures to_integer(0u32 - 1u32) == -1 by { apply(integer::uint32_subtract_to_integer(0u32, 1u32)); } }";
        assert!(verify_c_sources(underflow, &[]).is_err());
    }

    #[test]
    fn uint32_subtract_bridge_verifies_executed_c_difference() {
        let c = "unsigned int difference(unsigned int left, unsigned int right) { return left - right; }";
        let source = "import click::integer; verifying \"difference.c\"; uint32 difference(uint32 left, uint32 right) { requires right <= left; ensures to_integer(result) == to_integer(left) - to_integer(right); } by { step_until(function.exit); apply(integer::uint32_subtract_to_integer(left, right)); close(); }";
        verify_c_sources(source, &[("difference.c", c)]).unwrap();
        let expanded =
            expand_c_claim_source_by_label(source, &[("difference.c", c)], "difference.contract")
                .unwrap();
        verify_c_sources(&expanded, &[("difference.c", c)]).unwrap();
        for invalid in [
            source.replace("requires right <= left;", ""),
            source.replace("requires right <= left;", "requires defined(left - right);"),
            source.replace(
                "ensures to_integer(result) == to_integer(left) - to_integer(right);",
                "ensures to_integer(result) == to_integer(right) - to_integer(left);",
            ),
        ] {
            assert!(
                verify_c_sources(&invalid, &[("difference.c", c)]).is_err(),
                "{invalid}"
            );
        }
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 0.9s in the parallel gate"]
    fn uint64_integer_bridges_recheck_guards_full_width_and_expansion() {
        for (name, guard, goal) in [
            (
                "click::integer::uint64_add_to_integer",
                "to_integer(left) + to_integer(right) <= 18446744073709551615",
                "to_integer(left + right) == to_integer(left) + to_integer(right)",
            ),
            (
                "click::integer::uint64_multiply_to_integer",
                "to_integer(left) * to_integer(right) <= 18446744073709551615",
                "to_integer(left * right) == to_integer(left) * to_integer(right)",
            ),
            (
                "click::integer::uint64_subtract_to_integer",
                "to_integer(right) <= to_integer(left)",
                "to_integer(left - right) == to_integer(left) - to_integer(right)",
            ),
            (
                "click::integer::uint64_divide_to_integer",
                "right != 0u64; requires to_integer(right) != 0",
                "to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right))",
            ),
            (
                "click::integer::uint64_remainder_to_integer",
                "right != 0u64; requires to_integer(right) != 0",
                "to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right))",
            ),
            (
                "click::integer::uint64_to_integer_less_equal_implies_less_equal",
                "to_integer(left) <= to_integer(right)",
                "left <= right",
            ),
        ] {
            let source = format!(
                "import click::integer; theorem bridge(left: uint64, right: uint64) {{ requires {guard}; ensures {goal} by {{ apply({name}(left, right)); }} }}"
            );
            verify_c_sources(&source, &[]).unwrap_or_else(|e| panic!("{name}: {}", e.message()));
            let expanded =
                expand_c_claim_source_by_label(&source, &[], "bridge.ensures_0").unwrap();
            verify_c_sources(&expanded, &[]).unwrap();
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
                assert!(verify_c_sources(&invalid, &[]).is_err(), "{invalid}");
            }
        }
    }

    // Both native operations and modular calls must preserve the mathematical
    // observation; omitting either evaluation domain must not prove a claim.
    #[test]
    fn uint32_division_bridges_verify_actual_operations_calls_and_expansion() {
        for (name, op, mathematical) in [
            (
                "click::integer::uint32_divide_to_integer",
                "/",
                "truncating_quotient",
            ),
            (
                "click::integer::uint32_remainder_to_integer",
                "%",
                "truncating_remainder",
            ),
        ] {
            let guard = "right != 0u32; requires to_integer(right) != 0";
            let goal = format!(
                "to_integer(result) == {mathematical}(to_integer(left), to_integer(right))"
            );
            let c = format!(
                "uint32 op(uint32 left, uint32 right) {{ return left {op} right; }} uint32 caller(uint32 left, uint32 right) {{ return op(left, right); }}"
            );
            let source = format!(
                "import click::integer; verifying \"op.c\"; uint32 op(uint32 left, uint32 right) {{ requires {guard}; ensures {goal}; }} by {{ apply({name}(left, right)); step_until(function.exit); close(); }} uint32 caller(uint32 left, uint32 right) {{ requires {guard}; ensures {goal}; }}"
            );
            verify_c_sources(&source, &[("op.c", &c)])
                .unwrap_or_else(|error| panic!("{}\n{source}", error.message()));
            let expanded =
                expand_c_claim_source_by_label(&source, &[("op.c", &c)], "op.ensures_0").unwrap();
            verify_c_sources(&expanded, &[("op.c", &c)]).unwrap();
            // `to_integer(right) != 0` and `right != 0` are one fact, so
            // either premise alone suffices and only dropping both fails.
            for redundant in [
                "requires right != 0u32;",
                "requires to_integer(right) != 0;",
            ] {
                verify_c_sources(&source.replace(redundant, ""), &[("op.c", &c)])
                    .unwrap_or_else(|error| panic!("{}\n{source}", error.message()));
            }
            assert!(
                verify_c_sources(
                    &source.replace(
                        "requires right != 0u32; requires to_integer(right) != 0;",
                        ""
                    ),
                    &[("op.c", &c)]
                )
                .is_err()
            );
            assert!(
                verify_c_sources(
                    &source.replace(&format!("ensures {goal};"), &format!("ensures {goal} + 1;")),
                    &[("op.c", &c)]
                )
                .is_err()
            );
        }
    }

    #[test]
    fn uint64_division_bridges_need_the_integer_domain() {
        for (name, op, mathematical) in [
            (
                "click::integer::uint64_divide_to_integer",
                "/",
                "truncating_quotient",
            ),
            (
                "click::integer::uint64_remainder_to_integer",
                "%",
                "truncating_remainder",
            ),
        ] {
            let source = format!(
                "import click::integer; theorem exact(left: uint64, right: uint64) {{ requires right != 0u64; requires to_integer(right) != 0; ensures to_integer(left {op} right) == {mathematical}(to_integer(left), to_integer(right)) by {{ apply({name}(left, right)); }} }}"
            );
            verify_c_sources(&source, &[]).unwrap();
            // The Integer disequality and the native one are one fact, so
            // either premise alone suffices and only dropping both fails.
            for redundant in [
                "requires right != 0u64;",
                "requires to_integer(right) != 0;",
            ] {
                verify_c_sources(&source.replace(redundant, ""), &[]).unwrap();
            }
            assert!(
                verify_c_sources(
                    &source.replace(
                        "requires right != 0u64; requires to_integer(right) != 0;",
                        ""
                    ),
                    &[]
                )
                .is_err()
            );
        }
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 0.8s in the parallel gate"]
    fn uint64_integer_bridges_verify_actual_c_operations_and_modular_calls() {
        for (name, guard, goal, op) in [
            (
                "click::integer::uint64_add_to_integer",
                "to_integer(left) + to_integer(right) <= 18446744073709551615",
                "to_integer(left + right) == to_integer(left) + to_integer(right)",
                "+",
            ),
            (
                "click::integer::uint64_multiply_to_integer",
                "to_integer(left) * to_integer(right) <= 18446744073709551615",
                "to_integer(left * right) == to_integer(left) * to_integer(right)",
                "*",
            ),
            (
                "click::integer::uint64_subtract_to_integer",
                "to_integer(right) <= to_integer(left)",
                "to_integer(left - right) == to_integer(left) - to_integer(right)",
                "-",
            ),
            (
                "click::integer::uint64_divide_to_integer",
                "right != 0u64; requires to_integer(right) != 0",
                "to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right))",
                "/",
            ),
            (
                "click::integer::uint64_remainder_to_integer",
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
                "import click::integer; verifying \"op.c\"; uint64 op(uint64 left, uint64 right) {{ requires {guard}; ensures {result_goal}; }} by {{ apply({name}(left, right)); step_until(function.exit); close(); }} uint64 caller(uint64 left, uint64 right) {{ requires {guard}; ensures {result_goal}; }}"
            );
            verify_c_sources(&source, &[("op.c", &c)])
                .unwrap_or_else(|e| panic!("{name}: {}", e.message()));
            let expanded =
                expand_c_claim_source_by_label(&source, &[("op.c", &c)], "op.ensures_0").unwrap();
            verify_c_sources(&expanded, &[("op.c", &c)]).unwrap();
            assert!(
                verify_c_sources(
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
                "click::integer::int32_to_integer_less_equal_implies_less_equal",
                "int32",
                "to_integer(left) <= to_integer(right)",
                "left <= right",
            ),
            (
                "click::integer::int64_to_integer_less_equal_implies_less_equal",
                "int64",
                "to_integer(left) <= to_integer(right)",
                "left <= right",
            ),
        ] {
            let source = format!(
                "import click::integer; theorem bridge(left: {ty}, right: {ty}) {{ requires {guard}; ensures {goal} by {{ apply({name}(left, right)); }} }}"
            );
            verify_c_sources(&source, &[]).unwrap();
            let expanded =
                expand_c_claim_source_by_label(&source, &[], "bridge.ensures_0").unwrap();
            verify_c_sources(&expanded, &[]).unwrap();
            for invalid in [
                source.replace(&format!("requires {guard};"), ""),
                source.replace(&format!("ensures {goal}"), "ensures left > right"),
            ] {
                assert!(verify_c_sources(&invalid, &[]).is_err());
            }
        }
    }

    #[test]
    fn contract_scalar_casts_check_all_supported_widths_and_recheck_expansion() {
        for ty in ["int32", "uint32", "int64", "uint64", "int128", "uint128"] {
            let source = format!(
                "theorem cast(x: {ty}) {{ ensures x as {ty} == x by {{ have x as {ty} == x by close(); close(); }} }}"
            );
            verify_c_sources(&source, &[]).unwrap();
            let expanded = expand_c_claim_source_by_label(&source, &[], "cast.ensures_0").unwrap();
            verify_c_sources(&expanded, &[]).unwrap();
            let historical = source.replace(&format!("x as {ty}"), &format!("old(x) as {ty}"));
            verify_c_sources(&historical, &[]).unwrap();
            let expanded =
                expand_c_claim_source_by_label(&historical, &[], "cast.ensures_0").unwrap();
            verify_c_sources(&expanded, &[]).unwrap();
            for invalid in [
                source.replace(&format!("x as {ty}"), &format!("x as ({ty} *)")),
                source.replace(&format!("x: {ty}"), "x: Integer"),
                source.replace("== x", "!= x"),
            ] {
                assert!(verify_c_sources(&invalid, &[]).is_err(), "{invalid}");
            }
        }
    }
    #[test]
    fn int64_integer_operation_applications_recheck_guards_and_expansion() {
        let (name, op) = ("click::integer::int64_subtract_to_integer", "-");
        let source = format!(
            "import click::integer; theorem exact(left: int64, right: int64) {{ requires defined(left {op} right); ensures to_integer(left {op} right) == to_integer(left) {op} to_integer(right) by {{ apply({name}(left, right)); }} }}"
        );
        verify_c_sources(&source, &[]).unwrap();
        let expanded = expand_c_claim_source_by_label(&source, &[], "exact.ensures_0").unwrap();
        verify_c_sources(&expanded, &[]).unwrap();
        for invalid in [
            source.replace(&format!("requires defined(left {op} right);"), ""),
            source.replace(" == ", " != "),
        ] {
            assert!(verify_c_sources(&invalid, &[]).is_err(), "{invalid}");
        }
    }
    #[test]
    #[cfg(not(feature = "fast-gate"))]
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
        verify_c_sources(source, &[]).unwrap();
        for label in [
            "derived_floor_from_remainder.ensures_0",
            "derived_floor_from_remainder.ensures_1",
            "derived_ceiling_from_remainder.ensures_0",
            "derived_ceiling_from_remainder.ensures_1",
        ] {
            let expanded = expand_c_claim_source_by_label(source, &[], label).unwrap();
            verify_c_sources(&expanded, &[]).unwrap();
        }
    }

    #[test]
    fn integer_multiply_add_rechecks_application_and_expansion() {
        let source = "import click::integer; theorem distribute(a: Integer, b: Integer, c: Integer) { ensures (a + b) * c == a * c + b * c by { apply(integer::multiply_add(a, b, c)); } }";
        let verify_explicit = |source: &str| {
            crate::surface::proof::without_implicit_solve(|| verify_c_sources(source, &[]))
        };
        verify_explicit(source).unwrap();
        let expanded = expand_c_claim_source_by_label(source, &[], "distribute.ensures_0").unwrap();
        verify_explicit(&expanded).unwrap();
        for invalid in [
            source.replace("a * c + b * c", "a * c + b"),
            source.replace("multiply_add(a, b, c)", "multiply_add(a, c, b)"),
            source.replace("multiply_add(a, b, c)", "multiply_add(a, b)"),
            source.replace(": Integer", ": int32"),
        ] {
            assert!(verify_explicit(&invalid).is_err(), "{invalid}");
        }
    }

    #[test]
    fn integer_truncation_applications_recheck_guards_claims_and_expansion() {
        for (name, requirements, goal) in [
            (
                "click::integer::truncation_identity",
                &["d != 0"][..],
                "n == truncating_quotient(n, d) * d + truncating_remainder(n, d)",
            ),
            (
                "click::integer::positive_divisor_remainder_lower",
                &["d != 0", "0 < d"][..],
                "1 - d <= truncating_remainder(n, d)",
            ),
            (
                "click::integer::positive_divisor_remainder_upper",
                &["d != 0", "0 < d"][..],
                "truncating_remainder(n, d) <= d - 1",
            ),
            (
                "click::integer::nonnegative_dividend_remainder",
                &["d != 0", "0 <= n"][..],
                "0 <= truncating_remainder(n, d)",
            ),
            (
                "click::integer::nonpositive_dividend_remainder",
                &["d != 0", "n <= 0"][..],
                "truncating_remainder(n, d) <= 0",
            ),
        ] {
            let requires = requirements
                .iter()
                .map(|r| format!("requires {r}; "))
                .collect::<String>();
            let source = format!(
                "import click::integer; theorem law(n: Integer, d: Integer) {{ {requires}ensures {goal} by {{ apply({name}(n, d)); }} }}"
            );
            verify_c_sources(&source, &[]).unwrap();
            let expanded = expand_c_claim_source_by_label(&source, &[], "law.ensures_0").unwrap();
            verify_c_sources(&expanded, &[]).unwrap();
            for guard in requirements {
                let invalid = source.replace(&format!("requires {guard};"), "");
                if *guard == "d != 0" && requirements.contains(&"0 < d") {
                    verify_c_sources(&invalid, &[])
                        .expect("the entry solver derives nonzero from a positive divisor");
                } else {
                    assert!(verify_c_sources(&invalid, &[]).is_err(), "{invalid}");
                }
            }
            let invalid = source.replace(&format!("ensures {goal}"), "ensures n == d");
            assert!(verify_c_sources(&invalid, &[]).is_err(), "{invalid}");
        }
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
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
        verify_c_sources(source, &[]).unwrap();
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
            let expanded = expand_c_claim_source_by_label(source, &[], label).unwrap();
            verify_c_sources(&expanded, &[]).unwrap();
        }
        let guarded = "import click::integer; theorem use_order(a: Integer, b: Integer, c: Integer) { requires a <= b; requires 0 <= c; ensures a * c <= b * c by { apply(integer::multiply_order_nonnegative(a,b,c)); } }";
        verify_c_sources(guarded, &[]).unwrap();
        for bad in [
            guarded.replace("requires a <= b;", ""),
            guarded.replace("requires 0 <= c;", ""),
            guarded.replace("requires 0 <= c;", "requires c <= 0;"),
            guarded.replace("ensures a * c <= b * c", "ensures b * c <= a * c"),
        ] {
            assert!(verify_c_sources(&bad, &[]).is_err(), "{bad}");
        }
        for requirement in [
            "requires -9223372036854775808 <= fee;",
            "requires fee <= 9223372036854775807;",
            "requires 0 <= at_size;",
            "requires at_size <= size;",
        ] {
            assert!(
                verify_c_sources(&source.replace(requirement, ""), &[]).is_err(),
                "{requirement}"
            );
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
        verify_c_sources(source, &[]).unwrap();
        for label in [
            "checked_quotient_lower.ensures_0",
            "checked_quotient_upper.ensures_0",
            "use_scaled_quotient.ensures_0",
            "use_scaled_quotient.ensures_1",
        ] {
            let expanded = expand_c_claim_source_by_label(source, &[], label).unwrap();
            verify_c_sources(&expanded, &[]).unwrap();
        }
        let guarded = "import click::integer; theorem lower(x: int64, d: Integer) { requires defined(x + 1i64); requires d != 0; requires 1 <= d; requires -100 * d <= to_integer(x) + 1; ensures -100 <= truncating_quotient(to_integer(x + 1i64), d) by { have to_integer(x + 1i64) == to_integer(x) + 1; have -100 * d <= to_integer(x + 1i64) by { rewrite(to_integer(x + 1i64), to_integer(x) + 1); close(); } apply(integer::positive_divisor_quotient_lower(to_integer(x + 1i64), d, -100)); } }";
        verify_c_sources(guarded, &[]).unwrap();
        for bad in [
            guarded.replace("requires defined(x + 1i64);", ""),
            guarded
                .replace("requires d != 0;", "")
                .replace("requires 1 <= d;", ""),
        ] {
            assert!(verify_c_sources(&bad, &[]).is_err(), "{bad}");
        }
        verify_c_sources(&guarded.replace("requires d != 0;", ""), &[])
            .expect("the entry solver derives nonzero from 1 <= d");
        // Written for the Integer parameters without `to_integer`, `x + 1i64`
        // is the exact sum, which owes no definedness.
        let exact = guarded
            .replace("to_integer(x + 1i64)", "x + 1i64")
            .replace("requires defined(x + 1i64);", "");
        verify_c_sources(&exact, &[]).unwrap();
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
        verify_c_sources(source, &[]).unwrap();
        for label in ["negated_lower.ensures_0", "negated_upper.ensures_0"] {
            let expanded = expand_c_claim_source_by_label(source, &[], label).unwrap();
            verify_c_sources(&expanded, &[]).unwrap();
        }
        for bad in [
            source.replace("requires not (n <= 0);", "requires n <= 0;"),
            source.replace("requires not (0 <= n);", "requires 0 <= n;"),
        ] {
            assert!(verify_c_sources(&bad, &[]).is_err());
        }
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
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
        verify_c_sources(source, &[]).unwrap();
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
            let expanded = expand_c_claim_source_by_label(source, &[], label).unwrap();
            verify_c_sources(&expanded, &[]).unwrap();
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
            assert!(verify_c_sources(&bad, &[]).is_err(), "missing {guard}");
        }
        for (from, to) in [
            ("bound * d < n", "bound * d <= n"),
            ("n < bound * d", "n <= bound * d"),
            ("bound < 0", "bound <= 0"),
            ("0 < bound", "0 <= bound"),
        ] {
            let bad = uses.replacen(&format!("requires {from};"), &format!("requires {to};"), 1);
            assert!(verify_c_sources(&bad, &[]).is_err(), "weakened {from}");
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
        verify_c_sources(source, &[]).unwrap();
        for label in [
            "derived_lower_correction_bound.ensures_0",
            "derived_upper_correction_bound.ensures_0",
            "use_lower_correction_bound.ensures_0",
            "use_upper_correction_bound.ensures_0",
        ] {
            let expanded = expand_c_claim_source_by_label(source, &[], label).unwrap();
            verify_c_sources(&expanded, &[]).unwrap();
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
                "import click::integer; theorem correction(n: Integer, d: Integer, q: Integer, r: Integer, bound: Integer) {{ {} ensures {goal} by {{ apply(integer::{which}_correction_bound(n, d, q, r, bound)); }} }}",
                premises
                    .iter()
                    .map(|p| format!("requires {p}; "))
                    .collect::<String>()
            );
            verify_c_sources(&source, &[]).unwrap();
            for premise in premises {
                let bad = source.replace(&format!("requires {premise};"), "");
                assert!(verify_c_sources(&bad, &[]).is_err(), "{bad}");
            }
            for bad in [
                source.replace(&format!("requires {sign};"), "requires r == 0;"),
                source.replace("n == q * d + r", "n == q * d + -r"),
            ] {
                assert!(verify_c_sources(&bad, &[]).is_err(), "{bad}");
            }
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
                "theorem pinned(x: Integer, b: Integer) {{ {bounds} ensures {goal} by {{ close() using {{ {}; }} }} }}",
                bounds.replace("requires ", "").trim_end_matches(';')
            );
            verify_c_sources(&source, &[]).unwrap_or_else(|error| panic!("{}", error.message()));
            let expanded =
                expand_c_claim_source_by_label(&source, &[], "pinned.ensures_0").unwrap();
            assert!(
                expanded.contains("click::integer::le_antisymmetric"),
                "{expanded}"
            );
            verify_c_sources(&expanded, &[]).unwrap();
            assert!(
                verify_c_sources(&source.replace("ensures x == b", "ensures x == b + 1"), &[])
                    .is_err()
            );
            assert!(
                verify_c_sources(
                    &expanded.replace("ensures x == b", "ensures x == b + 1"),
                    &[]
                )
                .is_err()
            );
        }
    }

    #[test]
    fn signed_int64_minimum_literal_preserves_type_and_round_trips() {
        let source = "theorem minimum() { ensures to_integer(-9223372036854775808i64) == -9223372036854775808 by { normalize(); } }";
        verify_c_sources(source, &[]).unwrap();
        let expanded = expand_c_claim_source_by_label(source, &[], "minimum.ensures_0").unwrap();
        verify_c_sources(&expanded, &[]).unwrap();
        for literal in [
            "9223372036854775808i64",
            "-9223372036854775809i64",
            "9223372036854775809i64",
        ] {
            assert!(
                verify_c_sources(&source.replace("-9223372036854775808i64", literal), &[]).is_err(),
                "{literal}"
            );
        }
        assert!(
            verify_c_sources(
                "theorem bad() { ensures defined(0i64 - 9223372036854775808i64) by { normalize(); } }",
                &[]
            )
            .is_err()
        );
        assert!(
            verify_c_sources(
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
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: observation/cast/shift/mask/conditional expansion and replay"]
    fn machine_observation_bridges_expand_without_normalize() {
        fn check_replay(source: &str) -> Result<(), String> {
            verify_c_sources(source, &[]).map_err(|e| format!("{source}\n{}", e.message()))?;
            let expanded = expand_c_claim_source_by_label(source, &[], "bridge.ensures_0")
                .map_err(|e| format!("{source}\n{}", e.message()))?;
            if expanded.contains("normalize(") {
                return Err(format!("{source}\n{expanded}"));
            }
            crate::surface::proof::without_implicit_solve(|| verify_c_sources(&expanded, &[]))
                .map(|_| ())
                .map_err(|e| format!("{expanded}\n{}", e.message()))
        }
        let mut failures = Vec::new();
        let mut replay = |source: &str| {
            if let Err(error) = check_replay(source) {
                failures.push(error);
            }
        };
        for (ty, min, max) in [
            ("int32", "-2147483648", "2147483647"),
            ("uint32", "0", "4294967295"),
            ("int64", "-9223372036854775808", "9223372036854775807"),
            ("uint64", "0", "18446744073709551615"),
        ] {
            for op in ["+", "-", "*"] {
                let exact = format!("(to_integer(x) {op} to_integer(y))");
                let lo = format!("{min} <= {exact}");
                let hi = format!("{exact} <= {max}");
                let source = format!(
                    "theorem bridge(x: {ty}, y: {ty}) {{ requires {lo}; requires {hi}; ensures to_integer(x {op} y) == {exact} by {{ close() using {{ {lo}; {hi}; }}; }} }}"
                );
                replay(&source);
                for missing in [&lo, &hi] {
                    if ty.starts_with("uint")
                        && ((op == "-" && missing == &hi) || (op != "-" && missing == &lo))
                    {
                        continue;
                    }
                    let remaining = if missing == &lo { &hi } else { &lo };
                    let omitted = source.replace(
                        &format!("using {{ {lo}; {hi}; }}"),
                        &format!("using {{ {remaining}; }}"),
                    );
                    assert!(verify_c_sources(&omitted, &[]).is_err(), "{omitted}");
                }
            }
            replay(&format!(
                "theorem bridge(x: {ty}) {{ ensures to_integer(x) <= {max} by close(); }}"
            ));
        }
        for (ty, min, max) in [
            ("int8", "-128", "127"),
            ("uint8", "0", "255"),
            ("int16", "-32768", "32767"),
            ("uint16", "0", "65535"),
            ("int32", "-2147483648", "2147483647"),
            ("uint32", "0", "4294967295"),
            ("int64", "-9223372036854775808", "9223372036854775807"),
            ("uint64", "0", "18446744073709551615"),
            (
                "int128",
                "-170141183460469231731687303715884105728",
                "170141183460469231731687303715884105727",
            ),
            ("uint128", "0", "340282366920938463463374607431768211455"),
        ] {
            replay(&format!(
                "theorem bridge(z: Integer) {{ requires {min} <= z; requires z <= {max}; ensures to_integer(to_{ty}(z)) == z by {{ close() using {{ {min} <= z; z <= {max}; }}; }} }}"
            ));
        }
        for source in [
            "theorem bridge(x: int32) { requires 0 <= x; requires x <= 255; ensures to_integer(x as uint8) == to_integer(x) by { close() using { 0 <= x; x <= 255; }; } }",
            "theorem bridge(x: uint64) { requires x <= 4294967295u64; ensures to_integer(x as uint32) == to_integer(x) by { close() using { x <= 4294967295u64; }; } }",
            "theorem bridge(x: int32) { requires 0 <= x; requires x <= 100; ensures to_integer(x << 2) <= 400 by { close() using { 0 <= x; x <= 100; }; } }",
            "theorem bridge(x: int32) { requires 3 <= x; requires x <= 100; ensures 12 <= to_integer(x << 2) by { close() using { 3 <= x; x <= 100; }; } }",
            "theorem bridge(x: int32) { requires -100 <= x; requires x <= 101; ensures to_integer(x >> 2) <= 25 by { close() using { -100 <= x; x <= 101; }; } }",
            "theorem bridge(x: int32) { requires -101 <= x; requires x <= 100; ensures -26 <= to_integer(x >> 2) by { close() using { -101 <= x; x <= 100; }; } }",
            "theorem bridge(x: uint64) { requires x <= 100u64; ensures to_integer(x << 2u64) <= 400 by { close() using { x <= 100u64; }; } }",
            "theorem bridge(x: uint64) { requires x <= 101u64; ensures to_integer(x >> 2u64) <= 25 by { close() using { x <= 101u64; }; } }",
            "theorem bridge(x: int32) { ensures (x & 255) <= 255 by close(); }",
            "theorem bridge(x: int32) { requires 0 <= x; requires x <= 100; ensures (x & 255) <= 100 by { close() using { 0 <= x; x <= 100; }; } }",
            "theorem bridge(x: int32) { requires 0 <= x; ensures (x & 255) <= x by { close() using { 0 <= x; }; } }",
            "theorem bridge(x: uint64) { requires x <= 100u64; ensures (x & 255u64) <= 100u64 by { close() using { x <= 100u64; }; } }",
            "theorem bridge(x: Integer, y: Integer) { requires x < y; ensures (if x < y { x } else { y }) == x by { close() using { x < y; }; } }",
            "theorem bridge(x: Integer, y: Integer) { requires x < y; requires x <= 100; ensures (if x < y { x + 1 } else { y }) <= 101 by { close() using { x < y; x <= 100; }; } }",
            "theorem bridge(x: int32, y: int32) { requires x < y; ensures (if x < y { x } else { y }) == x by { close() using { x < y; }; } }",
            "theorem bridge(x: Integer, y: Integer) { requires not x < y; ensures (if x < y { x } else { y }) == y by { close() using { not x < y; }; } }",
            "theorem bridge(x: int32) { ensures to_integer(255 & x) <= 255 by close(); }",
            "theorem bridge(x: uint64) { requires x <= 100u64; ensures to_integer(x << 0) <= 100 by { close() using { x <= 100u64; }; } }",
            "theorem bridge(x: uint64) { requires x <= 1u64; ensures to_integer(x << 63) <= 9223372036854775808 by { close() using { x <= 1u64; }; } }",
            "theorem bridge(x: uint64) { requires x <= 18446744073709551615u64; ensures to_integer(x >> 63) <= 1 by { close() using { x <= 18446744073709551615u64; }; } }",
        ] {
            replay(source);
        }
        for source in [
            "theorem bridge(x: int32) { requires 0 <= x; requires x <= 100; ensures to_integer(x << 2) <= 399 by { close() using { 0 <= x; x <= 100; }; } }",
            "theorem bridge(x: int32) { requires -101 <= x; requires x <= 100; ensures -25 <= to_integer(x >> 2) by { close() using { -101 <= x; x <= 100; }; } }",
            "theorem bridge(x: int32) { requires x <= 100; ensures (x & 255) <= 100 by { close() using { x <= 100; }; } }",
            "theorem bridge(x: Integer, y: Integer) { requires x < y; ensures (if x < y { x } else { y }) == x by { close() using { }; } }",
        ] {
            assert!(verify_c_sources(source, &[]).is_err(), "{source}");
        }
        assert!(failures.is_empty(), "{}", failures.join("\n\n"));
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: foundational machine bridge library proofs replay without solving"]
    fn machine_bridge_library_proofs_have_no_normalization_or_search() {
        let names = [
            "le_difference",
            "difference_le",
            "equal_difference",
            "equal_le",
            "uint32_add_to_integer",
            "uint32_subtract_to_integer",
            "uint64_add_to_integer",
            "uint64_subtract_to_integer",
            "uint64_multiply_to_integer",
            "int32_add_to_integer",
            "int32_subtract_to_integer",
            "int64_subtract_to_integer",
            "uint32_multiply_to_integer",
            "to_int8_round_trip",
            "to_uint8_round_trip",
            "to_int16_round_trip",
            "to_uint16_round_trip",
            "to_int32_round_trip",
            "to_uint32_round_trip",
            "to_int64_round_trip",
            "to_uint64_round_trip",
        ];
        let mut failures = Vec::new();
        for name in names {
            let source = library_declarations(include_str!("../../library/integer.click"), &[name]);
            assert!(!source.contains("normalize("), "{name}");
            assert!(!source.contains("solve("), "{name}");
            if let Err(e) = crate::surface::proof::without_implicit_solve(|| {
                verify_c_sources(&format!("import click::integer;\n{source}"), &[])
            }) {
                failures.push(format!("{name}: {}", e.message()));
            }
        }
        assert!(failures.is_empty(), "{}", failures.join("\n\n"));
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: derived algebra and quotient library proofs replay without solving"]
    fn integer_algebra_library_proofs_have_no_normalization_or_search() {
        for name in [
            "multiply_add_left",
            "negate_as_product",
            "multiply_swap_front",
            "nonnegative_quotient_from_remainder",
            "nonnegative_quotient_shift",
        ] {
            let source = library_declarations(include_str!("../../library/integer.click"), &[name]);
            assert!(!source.contains("normalize("), "{name}");
            assert!(!source.contains("solve("), "{name}");
            crate::surface::proof::without_implicit_solve(|| {
                verify_c_sources(&format!("import click::integer;\n{source}"), &[])
            })
            .unwrap_or_else(|e| panic!("{name}: {}", e.message()));
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/surface/integer_conversions/tests.rs");
    }
}
