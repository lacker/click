//! Definition checking, framing, and scaling regressions for checked fold
//! read summaries. Each framing test builds its recorded history directly, so
//! the step a refusal names is pinned by the edge that produced it.

use super::*;
use crate::kernel::VerificationSession;

const ACCUMULATOR: Variable = Variable(3_200_000);
const ITEM: Variable = Variable(3_200_001);

fn name(text: &str) -> SpecExpression {
    SpecExpression::CExpression(CExpression::Variable(text.to_string()))
}

fn int(value: u32) -> SpecExpression {
    SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(value)))
}

fn item() -> SpecExpression {
    SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(ITEM)))
}

fn read_at(elements: SpecExpression) -> SpecExpression {
    SpecExpression::MemoryLoad {
        memory: SpecMemory::Current,
        pointer: Box::new(SpecExpression::PointerOffset {
            pointer: Box::new(name("v")),
            elements: Box::new(elements),
            byte_width: 4,
        }),
        value_type: CType::Int32,
    }
}

fn is_zero(value: SpecExpression) -> SpecProposition {
    SpecProposition::Comparison {
        left: value,
        operator: CComparisonOperator::Equal,
        right: int(0),
    }
}

/// `to_integer(if <read> == 0 { then } else { else })`.
fn counted(
    condition: SpecExpression,
    then: SpecExpression,
    otherwise: SpecExpression,
) -> SpecIntegerExpression {
    SpecIntegerExpression::FromMachine(Box::new(SpecExpression::If {
        condition: Box::new(is_zero(condition)),
        then_branch: Box::new(then),
        else_branch: Box::new(otherwise),
    }))
}

fn fold(
    start: SpecExpression,
    end: SpecExpression,
    initial: SpecIntegerExpression,
    step: SpecIntegerExpression,
) -> SpecIntegerExpression {
    SpecIntegerExpression::RangeFold {
        index: SpecIntegerRangeFoldIndex::Int32 {
            start: Box::new(start),
            end: Box::new(end),
        },
        initial: Box::new(initial),
        accumulator: ACCUMULATOR,
        item: ITEM,
        body: Box::new(SpecIntegerExpression::Add(
            Box::new(SpecIntegerExpression::Term(IntegerTerm::Variable(
                ACCUMULATOR,
            ))),
            Box::new(step),
        )),
    }
}

fn zero() -> SpecIntegerExpression {
    SpecIntegerExpression::Term(IntegerTerm::constant_i64(0))
}

/// The DFS example's `unmarked(v, lo, hi)`.
fn unmarked_body() -> SpecIntegerExpression {
    fold(
        name("lo"),
        name("hi"),
        zero(),
        counted(read_at(item()), int(1), int(0)),
    )
}

fn parameters() -> Vec<(String, CType)> {
    vec![
        ("v".to_string(), CType::Int32Pointer),
        ("lo".to_string(), CType::Int32),
        ("hi".to_string(), CType::Int32),
    ]
}

fn definition(body: SpecIntegerExpression) -> CFoldReadDefinition {
    CFoldReadDefinition::new("unmarked", parameters(), body)
}

fn check(body: SpecIntegerExpression) -> Result<CheckedFoldReadSummary, FoldReadDecline> {
    CheckedFoldReadSummary::check(&definition(body))
}

#[test]
fn the_unmarked_fold_admits_a_summary_of_its_own_interval() {
    let summary = check(unmarked_body()).expect("unmarked is in the checked subset");
    assert_eq!(summary.array_parameter, 0);
    assert_eq!(summary.start, FoldEndpointTemplate::Parameter(1));
    assert_eq!(summary.end, FoldEndpointTemplate::Parameter(2));
    assert_eq!(summary.element_width, 4);
}

#[test]
fn repeated_reads_in_the_condition_and_both_arms_are_one_support() {
    let body = fold(
        name("lo"),
        name("hi"),
        zero(),
        counted(read_at(item()), read_at(item()), read_at(item())),
    );
    check(body).expect("repeated exact reads are allowed");
}

#[test]
fn literal_endpoints_and_scalar_parameters_in_the_body_are_allowed() {
    let body = fold(
        int(0),
        name("hi"),
        SpecIntegerExpression::Term(IntegerTerm::constant_i64(7)),
        counted(read_at(item()), name("lo"), int(0)),
    );
    let summary = check(body).expect("literals and scalar parameters read no memory");
    assert_eq!(summary.start, FoldEndpointTemplate::Literal(0));
}

/// Every unsupported pattern the design names declines the whole definition.
#[test]
fn each_unsupported_read_pattern_declines_the_whole_definition() {
    let plus_one = SpecExpression::Add(Box::new(item()), Box::new(int(1)));
    let cases: Vec<(&str, SpecIntegerExpression, FoldReadDecline)> = vec![
        (
            "v[k + 1]",
            fold(
                name("lo"),
                name("hi"),
                zero(),
                counted(read_at(plus_one), int(1), int(0)),
            ),
            FoldReadDecline::ReadOutsideFoldIndex,
        ),
        (
            "v[v[k]]",
            fold(
                name("lo"),
                name("hi"),
                zero(),
                counted(read_at(read_at(item())), int(1), int(0)),
            ),
            FoldReadDecline::ReadOutsideFoldIndex,
        ),
        (
            "a branch reading v[hi]",
            fold(
                name("lo"),
                name("hi"),
                zero(),
                counted(read_at(item()), read_at(name("hi")), int(0)),
            ),
            FoldReadDecline::ReadOutsideFoldIndex,
        ),
        (
            "v passed to an opaque helper",
            fold(
                name("lo"),
                name("hi"),
                zero(),
                SpecIntegerExpression::PureFunctionApplication {
                    name: "helper".into(),
                    arguments: vec![SpecPureFunctionArgument::ArrayRef {
                        memory: SpecMemory::Current,
                        pointer: name("v"),
                        element_type: CType::Int32,
                    }],
                },
            ),
            FoldReadDecline::UnsupportedConstruct("a function call".into()),
        ),
        (
            "recursion",
            fold(
                name("lo"),
                name("hi"),
                zero(),
                SpecIntegerExpression::PureFunctionApplication {
                    name: "unmarked".into(),
                    arguments: vec![],
                },
            ),
            FoldReadDecline::UnsupportedConstruct("a function call".into()),
        ),
        (
            "a nested fold",
            fold(name("lo"), name("hi"), zero(), unmarked_body()),
            FoldReadDecline::UnsupportedConstruct("a nested fold".into()),
        ),
        (
            "a read in an endpoint",
            fold(
                name("lo"),
                read_at(int(0)),
                zero(),
                counted(read_at(item()), int(1), int(0)),
            ),
            FoldReadDecline::UnsupportedEndpoint,
        ),
        (
            "a read in the initial accumulator",
            fold(
                name("lo"),
                name("hi"),
                SpecIntegerExpression::FromMachine(Box::new(read_at(name("lo")))),
                counted(read_at(item()), int(1), int(0)),
            ),
            FoldReadDecline::UnsupportedInitialValue("it reads the array".into()),
        ),
        (
            "the array pointer used as a value",
            fold(
                name("lo"),
                name("hi"),
                zero(),
                counted(name("v"), int(1), int(0)),
            ),
            FoldReadDecline::UnsupportedConstruct("the array pointer used as a value".into()),
        ),
        (
            "a read at another program point",
            fold(
                name("lo"),
                name("hi"),
                zero(),
                counted(
                    SpecExpression::MemoryLoad {
                        memory: SpecMemory::FunctionEntry,
                        pointer: Box::new(SpecExpression::PointerOffset {
                            pointer: Box::new(name("v")),
                            elements: Box::new(item()),
                            byte_width: 4,
                        }),
                        value_type: CType::Int32,
                    },
                    int(1),
                    int(0),
                ),
            ),
            FoldReadDecline::UnsupportedConstruct("a read at another program point".into()),
        ),
        (
            "a byte-wide read",
            fold(
                name("lo"),
                name("hi"),
                zero(),
                counted(
                    SpecExpression::MemoryLoad {
                        memory: SpecMemory::Current,
                        pointer: Box::new(SpecExpression::PointerOffset {
                            pointer: Box::new(name("v")),
                            elements: Box::new(item()),
                            byte_width: 1,
                        }),
                        value_type: CType::UInt8,
                    },
                    int(1),
                    int(0),
                ),
            ),
            FoldReadDecline::ReadOutsideFoldIndex,
        ),
        (
            "the accumulator in the initial value",
            fold(
                name("lo"),
                name("hi"),
                SpecIntegerExpression::Term(IntegerTerm::Variable(ACCUMULATOR)),
                counted(read_at(item()), int(1), int(0)),
            ),
            FoldReadDecline::UnsupportedInitialValue("a free Integer variable".into()),
        ),
        (
            "not a fold",
            SpecIntegerExpression::FromMachine(Box::new(read_at(name("lo")))),
            FoldReadDecline::NotATopLevelInt32Fold,
        ),
    ];
    for (label, body, expected) in cases {
        assert_eq!(check(body), Err(expected), "{label}");
    }
}

#[test]
fn a_second_array_or_a_non_int32_parameter_declines() {
    let mut two_arrays = parameters();
    two_arrays.push(("w".to_string(), CType::Int32Pointer));
    assert!(matches!(
        CheckedFoldReadSummary::check(&CFoldReadDefinition::new(
            "unmarked",
            two_arrays,
            unmarked_body()
        )),
        Err(FoldReadDecline::UnsupportedParameters(_))
    ));
    let mut wide = parameters();
    wide.push(("x".to_string(), CType::Int64));
    assert!(matches!(
        CheckedFoldReadSummary::check(&CFoldReadDefinition::new("unmarked", wide, unmarked_body())),
        Err(FoldReadDecline::UnsupportedParameters(_))
    ));
}

#[test]
fn a_changed_body_under_one_name_poisons_the_session_and_a_new_session_rechecks() {
    {
        let _session = VerificationSession::enter();
        register_fold_read_definition(definition(unmarked_body()));
        assert!(registered_fold_read_summary("unmarked").is_ok());
        // Re-registering the same body is idempotent.
        register_fold_read_definition(definition(unmarked_body()));
        assert!(registered_fold_read_summary("unmarked").is_ok());
        let changed = fold(
            name("lo"),
            name("hi"),
            zero(),
            counted(read_at(item()), int(2), int(0)),
        );
        register_fold_read_definition(definition(changed));
        assert_eq!(
            registered_fold_read_summary("unmarked"),
            Err(FoldReadUnavailable::Conflicting)
        );
    }
    {
        // A fresh session forgets the old body, and a body that reads outside
        // its interval gets no summary under the same name.
        let _session = VerificationSession::enter();
        assert_eq!(
            registered_fold_read_summary("unmarked"),
            Err(FoldReadUnavailable::NotRegistered)
        );
        let outside = fold(
            name("lo"),
            name("hi"),
            zero(),
            counted(read_at(name("hi")), int(1), int(0)),
        );
        register_fold_read_definition(definition(outside));
        assert_eq!(
            registered_fold_read_summary("unmarked"),
            Err(FoldReadUnavailable::Declined(
                FoldReadDecline::ReadOutsideFoldIndex
            ))
        );
    }
}

// ---------------------------------------------------------------------------
// Framing
// ---------------------------------------------------------------------------

fn bv(variable: u32) -> Bitvector32Term {
    Bitvector32Term::Variable(Variable(u64::from(variable)))
}

/// An `int32` array parameter's base, spelled as the kernel spells one.
fn parameter_base(variable: u32) -> Pointer {
    Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(bv(variable), 4),
    }
}

fn element(base: &Pointer, index: Bitvector32Term) -> Pointer {
    Pointer {
        block: base.block.clone(),
        offset: PointerOffsetTerm::add(
            base.offset.clone(),
            PointerOffsetTerm::scale_int32(index, 4),
        ),
    }
}

fn byte_offset(pointer: &Pointer, bytes: i64) -> Pointer {
    Pointer {
        block: pointer.block.clone(),
        offset: PointerOffsetTerm::add(pointer.offset.clone(), PointerOffsetTerm::Constant(bytes)),
    }
}

fn one() -> CValue {
    CValue::Int32(Bitvector32Term::Constant(1))
}

fn application(
    memory: &CMemory,
    base: &Pointer,
    start: Bitvector32Term,
    end: Bitvector32Term,
) -> SharedIntegerApplication {
    SharedIntegerApplication::intern(
        "unmarked".into(),
        vec![
            PureFunctionArgument::ArrayRef {
                memory: memory.clone(),
                pointer: CValue::Pointer(CPointerValue::new(base.clone(), CType::Int32Pointer)),
                element_type: CType::Int32,
            },
            PureFunctionArgument::Value(CValue::Int32(start)),
            PureFunctionArgument::Value(CValue::Int32(end)),
        ],
    )
}

fn fact(condition: ConditionTerm) -> Proposition {
    Proposition::ConditionIs(condition, true)
}

fn le(left: Bitvector32Term, right: Bitvector32Term) -> Proposition {
    fact(ConditionTerm::Bitvector32SignedLessEqual(
        Box::new(left),
        Box::new(right),
    ))
}

fn lt(left: Bitvector32Term, right: Bitvector32Term) -> Proposition {
    fact(ConditionTerm::Bitvector32SignedLessThan(
        Box::new(left),
        Box::new(right),
    ))
}

fn context(facts: &[Proposition]) -> PureFactContext {
    facts
        .iter()
        .cloned()
        .fold(PureFactContext::new(), PureFactContext::assume_proposition)
}

fn register_unmarked() {
    register_fold_read_definition(definition(unmarked_body()));
}

fn frame(
    left: &SharedIntegerApplication,
    right: &SharedIntegerApplication,
    facts: &[Proposition],
) -> Result<usize, FoldFrameRefusal> {
    frame_fold_applications(left, right, &context(facts))
}

const V: u32 = 1_000;
const LO: u32 = 1_001;
const HI: u32 = 1_002;
const J: u32 = 1_003;
const N: u32 = 1_004;
const W: u32 = 1_005;

fn is_store_refusal(result: &Result<usize, FoldFrameRefusal>) -> bool {
    matches!(
        result,
        Err(FoldFrameRefusal::StepNotShownOutside { step: "store", .. })
    )
}

#[test]
fn a_store_at_the_exact_upper_endpoint_misses_the_prefix() {
    let _session = VerificationSession::enter();
    register_unmarked();
    let v = parameter_base(V);
    let before = CMemory::new();
    let after = before.clone().store(element(&v, bv(HI)), one());
    let old = application(&before, &v, Bitvector32Term::Constant(0), bv(HI));
    let new = application(&after, &v, Bitvector32Term::Constant(0), bv(HI));
    assert_eq!(frame(&old, &new, &[]), Ok(1));
    // Symmetric: the rule proves an equality.
    assert_eq!(frame(&new, &old, &[]), Ok(1));
}

#[test]
fn a_store_inside_the_range_is_refused() {
    let _session = VerificationSession::enter();
    register_unmarked();
    let v = parameter_base(V);
    let before = CMemory::new();
    // `v[hi - 1]`, the last cell of `[lo, hi)`.
    let last = Bitvector32Term::subtract(bv(HI), Bitvector32Term::Constant(1));
    let after = before.clone().store(element(&v, last.clone()), one());
    let old = application(&before, &v, bv(LO), bv(HI));
    let new = application(&after, &v, bv(LO), bv(HI));
    assert!(is_store_refusal(&frame(&old, &new, &[lt(bv(LO), bv(HI))])));
    // `v[lo]` with `lo < hi`.
    let after = before.clone().store(element(&v, bv(LO)), one());
    let new = application(&after, &v, bv(LO), bv(HI));
    assert!(is_store_refusal(&frame(&old, &new, &[lt(bv(LO), bv(HI))])));
}

#[test]
fn a_store_below_a_nonzero_lower_endpoint_needs_its_order_fact() {
    let _session = VerificationSession::enter();
    register_unmarked();
    let v = parameter_base(V);
    let before = CMemory::new();
    let after = before.clone().store(element(&v, bv(J)), one());
    let old = application(&before, &v, bv(LO), bv(HI));
    let new = application(&after, &v, bv(LO), bv(HI));
    assert_eq!(frame(&old, &new, &[lt(bv(J), bv(LO))]), Ok(1));
    // The missing bound is not guessed.
    assert!(is_store_refusal(&frame(&old, &new, &[])));
    // `j <= lo` is not enough: `j == lo` writes the first cell.
    assert!(is_store_refusal(&frame(&old, &new, &[le(bv(J), bv(LO))])));
    // `hi <= j` is the other side.
    assert_eq!(frame(&old, &new, &[le(bv(HI), bv(J))]), Ok(1));
}

#[test]
fn byte_widths_decide_partial_overlap_of_the_boundary_cells() {
    let _session = VerificationSession::enter();
    register_unmarked();
    let v = parameter_base(V);
    let before = CMemory::new();
    let old = application(&before, &v, bv(LO), bv(HI));
    let last = Bitvector32Term::subtract(bv(HI), Bitvector32Term::Constant(1));
    let wide = CValue::Int64(Bitvector32Term::Constant(0));
    // An eight-byte store at `v + 4*(hi - 1)` covers the last cell and the
    // endpoint cell. Nothing may separate it, even with `hi - 1 >= lo`.
    let after = before
        .clone()
        .store(element(&v, last.clone()), wide.clone());
    let new = application(&after, &v, bv(LO), bv(HI));
    assert!(is_store_refusal(&frame(
        &old,
        &new,
        &[le(bv(LO), last.clone())]
    )));
    // An eight-byte store at the endpoint cell starts past the last cell.
    let after = before.clone().store(element(&v, bv(HI)), wide.clone());
    let new = application(&after, &v, bv(LO), bv(HI));
    assert_eq!(frame(&old, &new, &[]), Ok(1));
    // One byte just below the endpoint cell is the last cell's top byte.
    let after = before.clone().store(
        byte_offset(&element(&v, bv(HI)), -1),
        CValue::UInt8(Bitvector32Term::Constant(7)),
    );
    let new = application(&after, &v, bv(LO), bv(HI));
    assert!(is_store_refusal(&frame(&old, &new, &[])));
    // An eight-byte store ending exactly at the first cell needs `j + 1 < lo`,
    // which this rule does not derive: it declines rather than guess.
    let after = before.clone().store(element(&v, bv(J)), wide);
    let new = application(&after, &v, bv(LO), bv(HI));
    assert!(is_store_refusal(&frame(&old, &new, &[lt(bv(J), bv(LO))])));
    // A two-byte store in the top half of the cell below the start misses it.
    let below = Bitvector32Term::subtract(bv(LO), Bitvector32Term::Constant(1));
    let after = before.clone().store(
        byte_offset(&element(&v, below.clone()), 2),
        CValue::Int16(Bitvector32Term::Constant(7)),
    );
    let new = application(&after, &v, bv(LO), bv(HI));
    assert_eq!(frame(&old, &new, &[lt(below, bv(LO))]), Ok(1));
}

#[test]
fn an_alias_needs_a_stated_separation_with_checked_membership() {
    let _session = VerificationSession::enter();
    register_unmarked();
    let a = parameter_base(V);
    let b = parameter_base(W);
    let before = CMemory::new();
    let after = before.clone().store(element(&b, bv(J)), one());
    let old = application(&before, &a, Bitvector32Term::Constant(0), bv(N));
    let new = application(&after, &a, Bitvector32Term::Constant(0), bv(N));
    // Distinct parameter names establish nothing: `a` and `b` may be one
    // object.
    assert!(is_store_refusal(&frame(&old, &new, &[])));
    let separate = Proposition::CResourceSeparate {
        left: CResource::Memory(CMemoryRange::new(
            a.clone(),
            Bitvector32Term::Constant(0),
            bv(N),
        )),
        right: CResource::Memory(CMemoryRange::new(
            b.clone(),
            Bitvector32Term::Constant(0),
            bv(N),
        )),
    };
    let in_b = [le(Bitvector32Term::Constant(0), bv(J)), lt(bv(J), bv(N))];
    let mut facts = vec![separate.clone()];
    facts.extend(in_b.iter().cloned());
    assert_eq!(frame(&old, &new, &facts), Ok(1));
    // The write must be shown inside the separated side.
    assert!(is_store_refusal(&frame(
        &old,
        &new,
        std::slice::from_ref(&separate)
    )));
    // And the interval inside the other: `[0, n + 1)` is not inside `[0, n)`.
    let longer = Bitvector32Term::add(bv(N), Bitvector32Term::Constant(1));
    let old_longer = application(&before, &a, Bitvector32Term::Constant(0), longer.clone());
    let new_longer = application(&after, &a, Bitvector32Term::Constant(0), longer);
    assert!(is_store_refusal(&frame(&old_longer, &new_longer, &facts)));
}

#[test]
fn changed_endpoints_or_base_pointers_are_not_framed() {
    let _session = VerificationSession::enter();
    register_unmarked();
    let v = parameter_base(V);
    let before = CMemory::new();
    let after = before.clone().store(element(&v, bv(HI)), one());
    let old = application(&before, &v, Bitvector32Term::Constant(0), bv(HI));
    let longer = Bitvector32Term::add(bv(HI), Bitvector32Term::Constant(1));
    let changed_end = application(&after, &v, Bitvector32Term::Constant(0), longer);
    assert!(matches!(
        frame(&old, &changed_end, &[]),
        Err(FoldFrameRefusal::ApplicationsDiffer { .. })
    ));
    let changed_base = application(
        &after,
        &parameter_base(W),
        Bitvector32Term::Constant(0),
        bv(HI),
    );
    assert!(matches!(
        frame(&old, &changed_base, &[]),
        Err(FoldFrameRefusal::ApplicationsDiffer { .. })
    ));
}

#[test]
fn an_empty_fold_crosses_any_store_only_when_emptiness_is_checked() {
    let _session = VerificationSession::enter();
    register_unmarked();
    let v = parameter_base(V);
    let before = CMemory::new();
    let after = before.clone().store(element(&v, bv(J)), one());
    let old = application(&before, &v, bv(LO), bv(HI));
    let new = application(&after, &v, bv(LO), bv(HI));
    assert_eq!(frame(&old, &new, &[le(bv(HI), bv(LO))]), Ok(1));
    // Unknown order is not emptiness.
    assert!(is_store_refusal(&frame(&old, &new, &[])));
    // `lo <= hi` is not emptiness either.
    assert!(is_store_refusal(&frame(&old, &new, &[le(bv(LO), bv(HI))])));
}

#[test]
fn a_lifetime_end_of_the_array_is_never_crossed() {
    let _session = VerificationSession::enter();
    register_unmarked();
    let block = PointerBlock::from("local:f:buffer");
    let base = Pointer {
        block: block.clone(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let declared = CMemory::new().with_block(block.clone(), 16);
    let ended = declared.without_local_block(&block);
    let old = application(
        &declared,
        &base,
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(0),
    );
    let new = application(
        &ended,
        &base,
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(0),
    );
    // Even an empty fold keeps the conservative lifetime rule.
    assert!(matches!(
        frame(&old, &new, &[]),
        Err(FoldFrameRefusal::StepNotShownOutside {
            step: "LocalLifetimeEnded",
            ..
        })
    ));
    // Another object's lifetime end is the block rule's to cross.
    let other = PointerBlock::from("local:f:other");
    let both = declared.clone().with_block(other.clone(), 4);
    let other_ended = both.without_local_block(&other);
    let old = application(
        &both,
        &base,
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(2),
    );
    let new = application(
        &other_ended,
        &base,
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(2),
    );
    assert_eq!(frame(&old, &new, &[]), Ok(1));
}

#[test]
fn a_call_is_framed_only_by_its_checked_write_set() {
    let _session = VerificationSession::enter();
    register_unmarked();
    let v = parameter_base(V);
    let before = CMemory::new();
    let havoc = |start: Bitvector32Term, end: Bitvector32Term| {
        before.clone().with_call_memory_havoc(
            Variable(2_000),
            &[CMemoryRange::new(v.clone(), start, end)],
            &PureFactContext::new(),
            None,
        )
    };
    let old = application(&before, &v, Bitvector32Term::Constant(0), bv(HI));
    // The callee may write `[hi, n)`: outside the prefix, once `hi <= n`.
    let after = havoc(bv(HI), bv(N));
    let new = application(&after, &v, Bitvector32Term::Constant(0), bv(HI));
    assert_eq!(frame(&old, &new, &[le(bv(HI), bv(N))]), Ok(1));
    // A reversed write set is not read as empty.
    assert!(matches!(
        frame(&old, &new, &[]),
        Err(FoldFrameRefusal::StepNotShownOutside { step: "call", .. })
    ));
    // `[hi - 1, n)` writes the last cell.
    let after = havoc(
        Bitvector32Term::subtract(bv(HI), Bitvector32Term::Constant(1)),
        bv(N),
    );
    let new = application(&after, &v, Bitvector32Term::Constant(0), bv(HI));
    assert!(matches!(
        frame(&old, &new, &[le(bv(HI), bv(N))]),
        Err(FoldFrameRefusal::StepNotShownOutside { step: "call", .. })
    ));
}

#[test]
fn sibling_and_unrelated_histories_and_unsummarized_functions() {
    let v = parameter_base(V);
    // A snapshot built in an earlier session carries no derivation here.
    let foreign = {
        let _session = VerificationSession::enter();
        CMemory::new().store(
            element(&v, bv(HI)),
            CValue::Int32(Bitvector32Term::Constant(2)),
        )
    };
    let _session = VerificationSession::enter();
    let base = CMemory::new();
    let left = base.clone().store(element(&v, bv(HI)), one());
    let right = base.clone().store(
        Pointer {
            block: PointerBlock::from("local:f:other"),
            offset: PointerOffsetTerm::Constant(0),
        },
        one(),
    );
    let old = application(&left, &v, Bitvector32Term::Constant(0), bv(HI));
    let new = application(&right, &v, Bitvector32Term::Constant(0), bv(HI));
    assert!(matches!(
        frame(&old, &new, &[]),
        Err(FoldFrameRefusal::NoSummary {
            reason: FoldReadUnavailable::NotRegistered,
            ..
        })
    ));
    register_unmarked();
    // Two siblings of one snapshot agree on the prefix when both steps back
    // to their common snapshot miss it.
    assert_eq!(frame(&old, &new, &[]), Ok(2));
    // A sibling that wrote inside the prefix does not.
    let inside = base
        .clone()
        .store(element(&v, Bitvector32Term::Constant(0)), one());
    let inside = application(&inside, &v, Bitvector32Term::Constant(0), bv(HI));
    assert!(is_store_refusal(&frame(
        &old,
        &inside,
        &[lt(Bitvector32Term::Constant(0), bv(HI))]
    )));
    // A snapshot with no recorded history reaches no common snapshot.
    let foreign = application(&foreign, &v, Bitvector32Term::Constant(0), bv(HI));
    assert!(matches!(
        frame(&old, &foreign, &[]),
        Err(FoldFrameRefusal::UnrelatedSnapshots { .. })
    ));
}

#[test]
fn a_declined_definition_frames_nothing_even_across_an_unrelated_store() {
    let _session = VerificationSession::enter();
    // `peek` reads `v[hi]` in its body: exactly the cell a store at the
    // endpoint writes. Its support is not narrowed to the fold's range.
    let peek = fold(
        name("lo"),
        name("hi"),
        zero(),
        counted(read_at(name("hi")), int(1), int(0)),
    );
    register_fold_read_definition(definition(peek));
    let v = parameter_base(V);
    let before = CMemory::new();
    let after = before.clone().store(element(&v, bv(HI)), one());
    let old = application(&before, &v, Bitvector32Term::Constant(0), bv(HI));
    let new = application(&after, &v, Bitvector32Term::Constant(0), bv(HI));
    assert!(matches!(
        frame(&old, &new, &[]),
        Err(FoldFrameRefusal::NoSummary {
            reason: FoldReadUnavailable::Declined(FoldReadDecline::ReadOutsideFoldIndex),
            ..
        })
    ));
}

#[test]
fn a_transport_rewrites_only_fold_application_snapshots() {
    let _session = VerificationSession::enter();
    register_unmarked();
    let v = parameter_base(V);
    let before = CMemory::new();
    let after = before.clone().store(element(&v, bv(HI)), one());
    let old = IntegerTerm::PureFunctionApplication(application(
        &before,
        &v,
        Bitvector32Term::Constant(0),
        bv(HI),
    ));
    let new = IntegerTerm::PureFunctionApplication(application(
        &after,
        &v,
        Bitvector32Term::Constant(0),
        bv(HI),
    ));
    let equals = |term: &IntegerTerm, value: i64| {
        fact(ConditionTerm::IntegerEqual(
            term.clone().into(),
            IntegerTerm::constant_i64(value).into(),
        ))
    };
    let facts = PureFactContext::new();
    let checked = frame_fold_application_transport(&equals(&old, 0), &equals(&new, 0), &facts)
        .expect("the zero count survives the endpoint store");
    assert_eq!(checked.framed_applications, 1);
    // A changed constant is not a frame.
    assert_eq!(
        frame_fold_application_transport(&equals(&old, 0), &equals(&new, 1), &facts).map(|_| ()),
        Err(FoldFrameRefusal::ShapeMismatch)
    );
    // Nothing to frame is not a success.
    assert_eq!(
        frame_fold_application_transport(&equals(&old, 0), &equals(&old, 0), &facts).map(|_| ()),
        Err(FoldFrameRefusal::NothingToFrame)
    );
    // The equality form: `old == old` carries to `old == new`.
    let reflexive = fact(ConditionTerm::IntegerEqual(
        old.clone().into(),
        old.clone().into(),
    ));
    let bridged = fact(ConditionTerm::IntegerEqual(
        old.clone().into(),
        new.clone().into(),
    ));
    frame_fold_application_transport(&reflexive, &bridged, &facts)
        .expect("the application equality is the checked bridge");
}

// ---------------------------------------------------------------------------
// Scaling
// ---------------------------------------------------------------------------

fn assert_linear(axis: &str, samples: &[(usize, usize)]) {
    eprintln!("{axis} (size, units): {samples:?}");
    for pair in samples.windows(2) {
        let [(small, small_work), (large, large_work)] = pair else {
            unreachable!()
        };
        let allowed = (*large as f64 / *small as f64) * 1.25;
        let ratio = *large_work as f64 / (*small_work).max(1) as f64;
        assert!(
            ratio <= allowed,
            "{axis}: work grew by {ratio:.2} from {small} to {large}, above {allowed:.2}: {samples:?}"
        );
    }
}

#[test]
fn summary_checking_is_linear_in_the_definition_body() {
    let mut samples = Vec::new();
    for size in [8usize, 16, 32, 64] {
        let step = (1..size).fold(counted(read_at(item()), int(1), int(0)), |step, _| {
            SpecIntegerExpression::Add(
                Box::new(step),
                Box::new(counted(read_at(item()), int(1), int(0))),
            )
        });
        let body = fold(name("lo"), name("hi"), zero(), step);
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| check(body.clone()));
        result.expect("a long body of exact reads is in the subset");
        samples.push((size, work));
    }
    assert_linear("fold read summary check over body size", &samples);
}

#[test]
fn framing_is_linear_in_applications_and_ignores_unrelated_facts_and_interval_length() {
    // Number of applications: one conjunction of `size` framed equalities.
    let mut samples = Vec::new();
    for size in [8usize, 16, 32, 64] {
        let _session = VerificationSession::enter();
        register_unmarked();
        let v = parameter_base(V);
        let before = CMemory::new();
        let after = before.clone().store(element(&v, bv(HI)), one());
        let at = |memory: &CMemory, index: usize| {
            fact(ConditionTerm::IntegerEqual(
                IntegerTerm::PureFunctionApplication(application(
                    memory,
                    &v,
                    bv(10_000 + index as u32),
                    bv(HI),
                ))
                .into(),
                IntegerTerm::constant_i64(0).into(),
            ))
        };
        let conjunction = |memory: &CMemory| {
            (1..size).fold(at(memory, 0), |all, index| {
                Proposition::And(Box::new(all), Box::new(at(memory, index)))
            })
        };
        let (source, target) = (conjunction(&before), conjunction(&after));
        let facts = PureFactContext::new();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            frame_fold_application_transport(&source, &target, &facts)
        });
        assert_eq!(
            result
                .expect("every application is framed")
                .framed_applications,
            size
        );
        samples.push((size, work));
    }
    assert_linear("fold framing over application count", &samples);

    // Unrelated facts: one framing whose bound is an exact fact, beside a
    // growing number of unrelated order facts.
    let mut works = Vec::new();
    for size in [64usize, 128, 256, 512] {
        let _session = VerificationSession::enter();
        register_unmarked();
        let v = parameter_base(V);
        let before = CMemory::new();
        let after = before.clone().store(element(&v, bv(J)), one());
        let old = application(&before, &v, bv(LO), bv(HI));
        let new = application(&after, &v, bv(LO), bv(HI));
        let mut facts = vec![lt(bv(J), bv(LO))];
        for index in 0..size as u32 {
            facts.push(lt(bv(20_000 + index), bv(30_000 + index)));
        }
        let facts = context(&facts);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            frame_fold_applications(&old, &new, &facts)
        });
        assert_eq!(result, Ok(1));
        works.push((size, work));
    }
    eprintln!("fold framing beside unrelated facts (facts, units): {works:?}");
    assert!(
        works.iter().all(|(_, work)| *work == works[0].1),
        "framing work must not depend on unrelated facts: {works:?}"
    );

    // Numeric interval length: `[0, 10)` and `[0, 1_000_000_000)` cost the
    // same, because no step enumerates the range.
    let mut lengths = Vec::new();
    for length in [10u32, 1_000, 1_000_000, 1_000_000_000] {
        let _session = VerificationSession::enter();
        register_unmarked();
        let v = parameter_base(V);
        let before = CMemory::new();
        let end = Bitvector32Term::Constant(length);
        let after = before.clone().store(element(&v, end.clone()), one());
        let old = application(&before, &v, Bitvector32Term::Constant(0), end.clone());
        let new = application(&after, &v, Bitvector32Term::Constant(0), end);
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| frame(&old, &new, &[]));
        assert_eq!(result, Ok(1));
        lengths.push((length as usize, work));
    }
    eprintln!("fold framing over interval length (length, units): {lengths:?}");
    assert!(
        lengths.iter().all(|(_, work)| *work == lengths[0].1),
        "framing work must not depend on the numeric interval length: {lengths:?}"
    );
}

#[test]
fn repeated_framing_along_a_store_sequence_is_linear() {
    // A straight line of `size` stores above the prefix, with the prefix's
    // application checked across each store in turn: one step each, so the
    // whole sequence is linear rather than a quadratic history walk.
    let mut stepwise = Vec::new();
    let mut whole = Vec::new();
    for size in [16usize, 32, 64, 128] {
        let _session = VerificationSession::enter();
        register_unmarked();
        let v = parameter_base(V);
        let mut memories = vec![CMemory::new()];
        let mut facts = Vec::new();
        for index in 0..size as u32 {
            let written = bv(40_000 + index);
            facts.push(le(bv(HI), written.clone()));
            let next = memories
                .last()
                .unwrap()
                .clone()
                .store(element(&v, written), one());
            memories.push(next);
        }
        let facts = context(&facts);
        let applications = memories
            .iter()
            .map(|memory| application(memory, &v, Bitvector32Term::Constant(0), bv(HI)))
            .collect::<Vec<_>>();
        let (crossed, work) = crate::instrumentation::measure_deterministic_work(|| {
            applications
                .windows(2)
                .map(|pair| frame_fold_applications(&pair[0], &pair[1], &facts).unwrap())
                .sum::<usize>()
        });
        assert_eq!(crossed, size);
        stepwise.push((size, work));
        let (crossed, work) = crate::instrumentation::measure_deterministic_work(|| {
            frame_fold_applications(&applications[0], applications.last().unwrap(), &facts).unwrap()
        });
        assert_eq!(crossed, size);
        whole.push((size, work));
    }
    assert_linear("fold framing across each store of a sequence", &stepwise);
    assert_linear("fold framing across a whole store sequence", &whole);
}

#[test]
fn an_offset_pointer_is_read_by_its_exact_byte_offset() {
    let _session = VerificationSession::enter();
    register_unmarked();
    let v = parameter_base(V);
    // `w = v + 1`, so `w[i - 2]` is `v + 4 + 4*(i - 2)`: the last cell of
    // `[0, i)`. The offset is read exactly, constant included.
    let w = byte_offset(&v, 4);
    let index = Bitvector32Term::subtract(bv(HI), Bitvector32Term::Constant(2));
    let before = CMemory::new();
    let after = before.clone().store(element(&w, index.clone()), one());
    let old = application(&before, &v, Bitvector32Term::Constant(0), bv(HI));
    let new = application(&after, &v, Bitvector32Term::Constant(0), bv(HI));
    // With the index at or past the end, the write starts past the range.
    assert_eq!(frame(&old, &new, &[le(bv(HI), index.clone())]), Ok(1));
    // Without a fact the write is not placed at all.
    assert!(is_store_refusal(&frame(&old, &new, &[])));
    // `lo <= i - 2` with the prefix `[lo, i)` does not help either: the
    // write is four bytes above `v + 4*(i - 2)`, inside the range.
    let old = application(&before, &v, bv(LO), bv(HI));
    let new = application(&after, &v, bv(LO), bv(HI));
    assert!(is_store_refusal(&frame(&old, &new, &[le(bv(LO), index)])));
}
