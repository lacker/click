//! One byte, one name: a byte's single term is its unsigned read, and a
//! signed read is the two's-complement conversion of that term.

use super::*;

fn byte(offset: i64) -> Pointer {
    Pointer {
        block: PointerBlock::from("global:bytes"),
        offset: PointerOffsetTerm::Constant(offset),
    }
}

#[test]
fn a_signed_byte_read_is_the_conversion_of_the_unsigned_read() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = crate::kernel::intern_c_memory(CMemory::new());
    let unsigned = Bitvector32Term::memory_read(memory.clone(), byte(0), LoadKind::UInt8);
    let signed = Bitvector32Term::memory_read(memory.clone(), byte(0), LoadKind::Int8);
    assert_eq!(signed, Bitvector32Term::signed_byte(unsigned.clone()));
    assert_eq!(signed.signed_byte_operand(), Some(&unsigned));
    // Every other kind is its own load term.
    assert!(matches!(
        Bitvector32Term::memory_read(memory.clone(), byte(0), LoadKind::Int16),
        Bitvector32Term::MemoryLoad(_, _, LoadKind::Int16)
    ));
    // The canonical form names the one unsigned read in both.
    let canonical_signed =
        crate::kernel::canonical_form_of_load(memory.clone(), byte(0), LoadKind::Int8);
    let canonical_unsigned =
        crate::kernel::canonical_form_of_load(memory, byte(0), LoadKind::UInt8);
    assert_eq!(
        canonical_signed,
        Bitvector32Term::signed_byte(canonical_unsigned)
    );
    // Constants fold: the byte 0xC8 is -56 signed.
    assert_eq!(
        Bitvector32Term::signed_byte(Bitvector32Term::Constant(0xC8)),
        Bitvector32Term::Constant(-56i32 as u32)
    );
}

#[test]
fn a_raw_signed_byte_load_term_is_refused_a_name() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = crate::kernel::intern_c_memory(CMemory::new());
    let raw = Bitvector32Term::MemoryLoad(memory.clone(), Box::new(byte(0)), LoadKind::Int8);
    assert_eq!(crate::kernel::eval::load_variable_for_term(&raw), None);
    let unsigned = Bitvector32Term::MemoryLoad(memory, Box::new(byte(0)), LoadKind::UInt8);
    assert!(crate::kernel::eval::load_variable_for_term(&unsigned).is_some());
}

#[test]
fn signed_and_unsigned_symbolic_reads_of_one_byte_share_its_name() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = CMemory::new()
        .with_block("global:bytes", 4)
        .store(byte(1), CValue::UInt8(Bitvector32Term::Constant(7)));
    let read = |value_type| {
        let paths = evaluate_c_memory_load_paths(
            &memory,
            byte(0),
            value_type,
            Vec::new().into(),
            Vec::new(),
            &PureFactContext::new(),
            false,
            false,
            None,
            None,
        );
        assert_eq!(paths.len(), 1);
        match &paths[0].outcome {
            CExpressionOutcome::Value(value) => value.clone(),
            other => panic!("{other:?}"),
        }
    };
    let CValue::UInt8(unsigned) = read(CType::UInt8) else {
        panic!("an unsigned byte read is uint8");
    };
    let CValue::Int8(signed) = read(CType::Int8) else {
        panic!("a signed byte read is int8");
    };
    assert_eq!(signed.signed_byte_operand(), Some(&unsigned));
}

#[test]
fn signed_byte_intervals_follow_the_unsigned_byte() {
    let unsigned = Bitvector32Term::Variable(Variable(612_001));
    let signed = Bitvector32Term::signed_byte(unsigned.clone());
    let unconstrained = PureFactContext::new();
    assert_eq!(unconstrained.signed_interval(&signed), Some((-128, 127)));
    let low = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(unsigned.clone(), Bitvector32Term::Constant(100)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_greater_equal(unsigned.clone(), Bitvector32Term::Constant(0)),
            true,
        );
    assert_eq!(low.signed_interval(&signed), Some((0, 100)));
    let high = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(unsigned.clone(), Bitvector32Term::Constant(200)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(unsigned, Bitvector32Term::Constant(255)),
            true,
        );
    assert_eq!(high.signed_interval(&signed), Some((-56, -1)));
}

fn byte_load(offset: i64) -> Bitvector32Term {
    let memory = crate::kernel::intern_c_memory(CMemory::new());
    Bitvector32Term::memory_read(memory, byte(offset), LoadKind::UInt8)
}

fn equal(left: Bitvector32Term, right: i64) -> ConditionTerm {
    ConditionTerm::Bitvector32Equal(
        Box::new(left),
        Box::new(Bitvector32Term::Constant(right as i32 as u32)),
    )
}

fn equal_terms(left: Bitvector32Term, right: Bitvector32Term) -> ConditionTerm {
    ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right))
}

fn fact(condition: ConditionTerm) -> Proposition {
    Proposition::ConditionIs(condition, true)
}

/// The signed/unsigned pairs every byte test checks: both halves of the
/// range and both of its ends.
const BYTE_PAIRS: [(i64, i64); 7] = [
    (0, 0),
    (7, 7),
    (127, 127),
    (-128, 128),
    (-56, 200),
    (-1, 255),
    (-2, 254),
];

#[test]
fn a_signed_byte_constant_decides_its_unsigned_byte() {
    let _session = crate::kernel::VerificationSession::enter();
    let unsigned = byte_load(0);
    let signed = Bitvector32Term::signed_byte(unsigned.clone());
    for (signed_value, unsigned_value) in BYTE_PAIRS {
        let context =
            PureFactContext::new().assume_condition(equal(signed.clone(), signed_value), true);
        assert_eq!(
            context.known_signed_constant_after_normalization(&unsigned),
            Some(unsigned_value),
            "int8(u) == {signed_value}"
        );
        assert_eq!(
            context.decide(&equal(unsigned.clone(), unsigned_value)),
            Some(true)
        );
        // A different byte is refuted, not merely undecided.
        assert_eq!(
            context.decide(&equal(unsigned.clone(), (unsigned_value + 1) % 256)),
            Some(false)
        );
    }
}

#[test]
fn an_unsigned_byte_constant_decides_its_signed_read() {
    let _session = crate::kernel::VerificationSession::enter();
    let unsigned = byte_load(0);
    let signed = Bitvector32Term::signed_byte(unsigned.clone());
    for (signed_value, unsigned_value) in BYTE_PAIRS {
        let context =
            PureFactContext::new().assume_condition(equal(unsigned.clone(), unsigned_value), true);
        assert_eq!(
            context.known_signed_constant_after_normalization(&signed),
            Some(signed_value),
            "u == {unsigned_value}"
        );
        assert_eq!(
            context.decide(&equal(signed.clone(), signed_value)),
            Some(true)
        );
    }
}

#[test]
fn byte_constants_cross_equalities_with_symbolic_values_in_both_directions() {
    let _session = crate::kernel::VerificationSession::enter();
    let unsigned = byte_load(0);
    let signed = Bitvector32Term::signed_byte(unsigned.clone());
    let value = Bitvector32Term::Variable(Variable(612_101));
    // A call result equal to the signed read, with the byte known (the
    // forward direction a callee's `char` contract needs).
    let forward = PureFactContext::new()
        .assume_condition(equal_terms(value.clone(), signed.clone()), true)
        .assume_condition(equal(unsigned.clone(), 200), true);
    assert_eq!(
        forward.known_signed_constant_after_normalization(&value),
        Some(-56)
    );
    // The same facts in the other order settle the class by a union.
    let forward_after = PureFactContext::new()
        .assume_condition(equal(unsigned.clone(), 200), true)
        .assume_condition(equal_terms(value.clone(), signed.clone()), true);
    assert_eq!(
        forward_after.known_signed_constant_after_normalization(&value),
        Some(-56)
    );
    // The signed read equal to a value later known: a union settles the
    // signed read's class, which settles the byte.
    for (first, second) in [
        (
            equal_terms(signed.clone(), value.clone()),
            equal(value.clone(), 7),
        ),
        (
            equal(value.clone(), -56),
            equal_terms(signed.clone(), value.clone()),
        ),
    ] {
        let reverse = PureFactContext::new()
            .assume_condition(first.clone(), true)
            .assume_condition(second.clone(), true);
        let expected = reverse
            .known_signed_constant_after_normalization(&value)
            .map(|signed| i64::from(signed as i8 as u8));
        assert!(expected.is_some());
        assert_eq!(
            reverse.known_signed_constant_after_normalization(&unsigned),
            expected
        );
    }
    // A symbolic value alone settles nothing.
    let symbolic =
        PureFactContext::new().assume_condition(equal_terms(signed.clone(), value.clone()), true);
    assert_eq!(
        symbolic.known_signed_constant_after_normalization(&unsigned),
        None
    );
    assert_eq!(symbolic.decide(&equal(unsigned, 7)), None);
}

#[test]
fn an_out_of_range_signed_byte_constant_settles_no_byte() {
    let _session = crate::kernel::VerificationSession::enter();
    let unsigned = byte_load(0);
    let signed = Bitvector32Term::signed_byte(unsigned.clone());
    // `int8(u) == 200` is the conversion of no byte. It must not become the
    // satisfiable `u == 200` (nor `u == 200 mod 256` read any other way).
    for impossible in [200, 128, -129, 255, 256, -200] {
        let context =
            PureFactContext::new().assume_condition(equal(signed.clone(), impossible), true);
        assert_eq!(
            context.known_signed_constant_after_normalization(&unsigned),
            None,
            "int8(u) == {impossible}"
        );
        assert_ne!(
            context.decide(&equal(unsigned.clone(), impossible.rem_euclid(256))),
            Some(true)
        );
        let goal = fact(equal(unsigned.clone(), impossible.rem_euclid(256)));
        let premise = fact(equal(signed.clone(), impossible));
        assert!(!crate::kernel::proof::equality_rewrite::equality_rewrite_applies(&goal, &premise));
    }
}

#[test]
fn only_a_byte_load_is_settled_by_its_signed_conversion() {
    let _session = crate::kernel::VerificationSession::enter();
    // An operand that is not a byte load has no structural byte range, so
    // its conversion's constant folds forward but is never inverted.
    let operand = Bitvector32Term::Variable(Variable(612_201));
    let signed = Bitvector32Term::signed_byte(operand.clone());
    let context = PureFactContext::new().assume_condition(equal(signed.clone(), 7), true);
    assert_eq!(
        context.known_signed_constant_after_normalization(&operand),
        None
    );
    let goal = fact(equal(operand.clone(), 7));
    assert!(
        !crate::kernel::proof::equality_rewrite::equality_rewrite_applies(
            &goal,
            &fact(equal(signed.clone(), 7))
        )
    );
    let forward = PureFactContext::new().assume_condition(equal(operand, 200), true);
    assert_eq!(
        forward.known_signed_constant_after_normalization(&signed),
        Some(-56)
    );
}

#[test]
fn a_signed_byte_equality_rewrites_the_unsigned_byte() {
    let _session = crate::kernel::VerificationSession::enter();
    let unsigned = byte_load(0);
    let signed = Bitvector32Term::signed_byte(unsigned.clone());
    let premise = fact(equal(signed.clone(), -56));
    let available = vec![premise.clone()];
    let rewrite = |goal: Proposition| {
        crate::kernel::proof::equality_rewrite::rewrite_proposition_by_exact_equality(
            &goal, &premise, &available,
        )
    };
    // The unsigned read the written equality never mentions is reached.
    assert_eq!(
        rewrite(fact(equal(unsigned.clone(), 200))),
        Ok(fact(equal(Bitvector32Term::Constant(200), 200)))
    );
    // The signed read itself still rewrites to the stated constant.
    assert_eq!(
        rewrite(fact(equal(signed.clone(), -56))),
        Ok(fact(equal(Bitvector32Term::Constant(-56i32 as u32), -56)))
    );
    // A symbolic right side is an ordinary equality, rewritten as written.
    let value = Bitvector32Term::Variable(Variable(612_301));
    let symbolic = fact(equal_terms(signed.clone(), value.clone()));
    assert_eq!(
        crate::kernel::proof::equality_rewrite::rewrite_proposition_by_exact_equality(
            &fact(equal(signed, 1)),
            &symbolic,
            std::slice::from_ref(&symbolic),
        ),
        Ok(fact(equal(value, 1)))
    );
    assert!(
        !crate::kernel::proof::equality_rewrite::equality_rewrite_applies(
            &fact(equal(unsigned, 1)),
            &symbolic
        )
    );
}
