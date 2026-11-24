use super::*;

fn prove(body: &str) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    verify_c_sources(
        &format!("verifying \"literals.rs\"; {body}"),
        &[("literals.rs", "")],
    )
}

#[test]
fn rust_integer_literals_preserve_native_types_and_signed_boundaries() {
    for (ty, min, max) in [
        ("i8", "128", "127"),
        ("i16", "32768", "32767"),
        ("i32", "2147483648", "2147483647"),
        ("i64", "9223372036854775808", "9223372036854775807"),
        ("isize", "9223372036854775808", "9223372036854775807"),
    ] {
        prove(&format!(
            "theorem limits() {{
            ensures -{min}{ty} < 0{ty} by {{ normalize(); }}
            ensures {max}{ty} > 0{ty} by {{ normalize(); }}
            ensures -(({min}{ty})) == -{min}{ty} by {{ normalize(); }}
        }}"
        ))
        .unwrap_or_else(|error| panic!("{ty}: {error:?}"));
    }
    for (ty, max) in [
        ("u8", "255"),
        ("u16", "65535"),
        ("u32", "4294967295"),
        ("u64", "18446744073709551615"),
        ("usize", "18446744073709551615"),
    ] {
        prove(&format!(
            "theorem limits() {{ ensures {max}{ty} > 0{ty} by {{ normalize(); }} }}"
        ))
        .unwrap_or_else(|error| panic!("{ty}: {error:?}"));
    }
    // In particular, explicit i64 must retain its type even at the i32 boundary.
    prove("function large() -> i64 { -2147483648i64 }
           theorem width() { ensures large() == -2147483648i64 by { unfold(large()); normalize(); } }")
        .unwrap();
}

#[test]
fn rust_integer_radices_and_separators_verify() {
    prove(
        r#"theorem spelling_boundaries() {
        ensures 0xff_ff_u16 == 65535u16 by { normalize(); }
        ensures 0b__1__u32 == 1u32 by { normalize(); }
        ensures 0o7_7u8 == 63u8 by { normalize(); }
        ensures -0x8000_0000i32 < 0i32 by { normalize(); }
        ensures -(0x8000_0000_0000_0000isize) < 0isize by { normalize(); }
    }
    theorem mathematical(value: Integer) {
        requires value == 0x1_0000_0000_0000_0000;
        ensures value == 18_446_744_073_709_551_616 by { close(); }
    }"#,
    )
    .unwrap();
    assert!(
        prove("theorem false_claim() { ensures 0xffu8 == 254u8 by { normalize(); } }").is_err()
    );
    assert!(
        prove("theorem false_claim() { ensures 0x1_0000 == 0u16 by { normalize(); } }").is_err()
    );
}

#[test]
fn rust_integer_literals_reject_overflow_and_invalid_spellings() {
    for (literal, message) in [
        ("128i8", "out of range for `i8`"),
        ("-129i8", "out of range for `i8`"),
        ("32768i16", "out of range for `i16`"),
        ("-32769i16", "out of range for `i16`"),
        ("2147483648i32", "out of range for `i32`"),
        ("-(2147483648i32 + 0i32)", "out of range for `i32`"),
        ("-2147483649i32", "out of range for `i32`"),
        ("9_223_372_036_854_775_808i64", "out of range for `i64`"),
        ("-9_223_372_036_854_775_809i64", "out of range for `i64`"),
        ("9223372036854775808isize", "out of range for `isize`"),
        ("-9223372036854775809isize", "out of range for `isize`"),
        ("256_u8", "out of range for `u8`"),
        ("65536u16", "out of range for `u16`"),
        ("0x1_0000_0000u32", "out of range for `u32`"),
        ("0x1_0000_0000_0000_0000u64", "out of range for `u64`"),
        ("18446744073709551616usize", "out of range for `usize`"),
        ("-1usize", "cannot negate a `usize`"),
        ("-1u32", "cannot negate a `u32`"),
        ("0b102u8", "invalid base-2"),
        ("0o89u16", "invalid base-8"),
        ("0x_u32", "invalid base-16"),
        ("1u128", "unsupported integer literal suffix `u128`"),
        ("1i128", "unsupported integer literal suffix `i128`"),
        ("1f32", "unsupported integer literal suffix `f32`"),
        ("1u16oops", "unsupported integer literal suffix `u16oops`"),
    ] {
        let source = format!(
            "verifying \"literals.rs\"; theorem bad() {{ ensures {literal} == {literal}; }}"
        );
        let error = parser::parse(&source).expect_err(literal);
        assert!(error.message().contains(message), "{literal}: {error:?}");
    }
}

#[test]
fn rust_integer_literal_syntax_does_not_change_c_or_cpp_sidecars() {
    for language in ["c", "cpp"] {
        for literal in ["65_535", "0xff", "0b10", "0o77", "1u16", "1usize", "1i32"] {
            let source = format!(
                "verifying \"source.{language}\"; theorem bad() {{ ensures {literal} == {literal}; }}"
            );
            let error = parser::parse(&source).unwrap_err();
            assert!(
                error.message().contains("requires a Rust sidecar"),
                "{error:?}"
            );
        }
    }
    verify_c_sources(
        "verifying \"source.c\"; theorem legacy() {
        ensures 255u8 > 0u8 by { normalize(); }
        ensures 4294967295u32 > 0u32 by { normalize(); }
        ensures -9223372036854775808i64 < 0i64 by { normalize(); }
        ensures 18446744073709551615u64 > 0u64 by { normalize(); }
    }",
        &[("source.c", "")],
    )
    .unwrap();
}

#[test]
fn rust_shift_contracts_wrap_bits_and_preserve_the_operand_width() {
    for claim in [
        "(-1i32 << 1u32) == -2i32",
        "(1073741824i32 << 1u32) == -2147483648i32",
        "(-1i64 << 1u32) == -2i64",
        "(4611686018427387904i64 << 1u32) == -9223372036854775808i64",
        "(64i8 << 1u32) == -128i8",
        "(16384i16 << 1u32) == -32768i16",
        "(128u8 << 1u32) == 0u8",
        "(-128i8 >> 7u32) == -1i8",
    ] {
        prove(&format!(
            "theorem shift() {{ ensures {claim} by {{ normalize(); }} }}"
        ))
        .unwrap_or_else(|error| panic!("{claim}: {error:?}"));
    }
    for expression in [
        "1i8 << 8u32",
        "1i16 << 16u32",
        "1i32 << 32u32",
        "1i64 << 64u32",
        "1u8 >> 8u32",
        "1i16 >> 16u32",
        "1i32 << -1i32",
        "1i32 << 4294967296u64",
        "1i64 >> -1i32",
    ] {
        assert!(prove(&format!("theorem invalid() {{ ensures ({expression}) == ({expression}) by {{ normalize(); }} }}")).is_err(), "{expression}");
    }
    for expression in ["-1 << 1", "1073741824 << 1"] {
        assert!(verify_click_theorems(&format!("theorem c_shift() {{ ensures ({expression}) == ({expression}) by {{ normalize(); }} }}")).is_err(), "C signed shift domain: {expression}");
    }
}

#[test]
fn rust_shift_spelling_survives_expansion_and_rechecking() {
    let source = r#"verifying "literals.rs";
        theorem rust_shift(x: i8) {
            ensures (x << 1u32) == (x << 1u32) by { normalize(); }
        }
    "#;
    let sources = [("literals.rs", "")];
    verify_c_sources(source, &sources).unwrap();
    let expanded =
        expand_c_claim_source_by_label(source, &sources, "rust_shift.ensures_0").unwrap();
    assert!(expanded.contains("<<"), "{expanded}");
    crate::surface::proof::without_implicit_solve(|| verify_c_sources(&expanded, &sources))
        .unwrap();
}

#[test]
fn rust_shift_source_identity_survives_printing_and_resource_arguments() {
    for (operator, left_shift) in [("<<", true), (">>", false)] {
        let source = format!(
            "verifying \"shift.rs\"; function shifted(x: i32, n: i32) -> i32 {{ x {operator} n }}"
        );
        let parsed = parser::parse(&source).unwrap();
        let expression = parsed.click_function_definitions()[0].body().unwrap();
        assert!(matches!(
            (expression, left_shift),
            (ContractExpression::RustShiftLeft(..), true)
                | (ContractExpression::RustShiftRight(..), false)
        ));
        let argument =
            crate::surface::lowering::resource_argument_to_program_expression(expression)
                .expect("resource arguments retain the source shift");
        assert!(matches!(
            (argument, left_shift),
            (ProgramExpression::RustShiftLeft(..), true)
                | (ProgramExpression::RustShiftRight(..), false)
        ));
        let spelled = crate::surface::diagnostics::describe_contract_expression(expression);
        let reparsed = parser::parse(&format!(
            "verifying \"shift.rs\"; function shifted(x: i32, n: i32) -> i32 {{ {spelled} }}"
        ))
        .unwrap();
        assert_eq!(
            reparsed.click_function_definitions()[0].body().unwrap(),
            expression
        );
        let c = parser::parse(&format!(
            "function shifted(x: int32, n: int32) -> int32 {{ x {operator} n }}"
        ))
        .unwrap();
        assert!(matches!(
            (
                c.click_function_definitions()[0].body().unwrap(),
                left_shift
            ),
            (ContractExpression::ShiftLeft(..), true) | (ContractExpression::ShiftRight(..), false)
        ));
    }
}
