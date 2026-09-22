//! Message-shape regressions for the unestablished-condition refusal.
//!
//! The `.click` fixtures in `mdtests/` pin the two forms a source file can
//! reach. These cover the expression forms whose call sites no `.click` source
//! currently reaches, and the spellings a reader depends on.

use super::*;

/// `probe(p, index)` with `p` an external `int32*` argument and `index`
/// symbolic: the shape a pure theorem's parameters reach a lowering in.
fn indexed_pointer_site() -> (BTreeMap<String, CValue>, CState) {
    let pointer = CValue::typed_pointer(
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(Variable(100_000))),
                byte_width: 4,
            },
        },
        CType::Int32Pointer,
    );
    let values = BTreeMap::from([
        ("p".to_string(), pointer),
        (
            "index".to_string(),
            CValue::Int32(Bitvector32Term::Variable(Variable(1))),
        ),
    ]);
    (values, CState::new())
}

/// The pointer `p` was passed, as the kernel holds it.
fn pointer_base(values: &BTreeMap<String, CValue>) -> Pointer {
    let CValue::Pointer(pointer) = &values["p"] else {
        unreachable!("the probe binds `p` to a pointer");
    };
    pointer.pointer().clone()
}

/// The cell `p[index]`, as the kernel indexes it.
fn indexed_cell(values: &BTreeMap<String, CValue>) -> Pointer {
    Pointer {
        block: pointer_base(values).block,
        offset: PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(Variable(100_000))),
                byte_width: 4,
            }),
            Box::new(PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(Variable(1))),
                byte_width: 4,
            }),
        ),
    }
}

fn unproved(proposition: Proposition) -> Vec<crate::kernel::ProofObligation> {
    vec![crate::kernel::ProofObligation::verification_condition(
        proposition,
    )]
}

/// A witness value or theorem argument is an expression, not a proposition;
/// the refusal must call it one and still name its subterm and its repair.
#[test]
fn an_expression_form_names_itself_its_cell_and_its_repair() {
    let (values, state) = indexed_pointer_site();
    let expression = ContractExpression::Call {
        name: "to_integer".to_string(),
        arguments: vec![ContractExpression::CFragment(CExpression::TypedLoad {
            pointer: Box::new(CExpression::Add(
                Box::new(CExpression::Variable("p".to_string())),
                Box::new(CExpression::Variable("index".to_string())),
            )),
            value_type: CType::Int32,
            volatile: false,
            pointee_constant: false,
            source: Default::default(),
        })],
    };
    let site = StatedSite::new(StatedForm::Expression(&expression), &state, &values);
    let message = refuse_unproved_conversion_bounds(
        &unproved(Proposition::CMemoryLoadable {
            memory: state.memory().clone(),
            base: indexed_cell(&values),
            bytes: Bitvector32Term::Constant(4),
        }),
        &PureFactContext::new(),
        &site,
    )
    .expect_err("an unproved mandatory condition is refused");
    assert!(message.starts_with("the expression `"), "{message}");
    assert!(
        message.contains("its subterm `p[index]` denotes a value only where 1 condition"),
        "{message}"
    );
    assert!(
        message.contains("the 4 bytes at `p[index]` must be viewable"),
        "{message}"
    );
    assert!(
        message.contains("`viewable(p[index..index + 1])`"),
        "{message}"
    );
    assert!(message.contains("premises consulted: none"), "{message}");
}

/// A segment bound or resource quantity is a C fragment. Its refusal reads the
/// same, and the premises it consulted are listed in the user's names.
#[test]
fn a_c_fragment_form_lists_the_premises_it_consulted() {
    let (values, state) = indexed_pointer_site();
    let expression = CExpression::Variable("index".to_string());
    let site = StatedSite::new(StatedForm::CFragment(&expression), &state, &values);
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(
                Box::new(Bitvector32Term::Constant(0)),
                Box::new(Bitvector32Term::Variable(Variable(1))),
            ),
            true,
        ))
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: state.memory().clone(),
            base: pointer_base(&values),
            bytes: Bitvector32Term::Multiply(
                Box::new(Bitvector32Term::Variable(Variable(1))),
                Box::new(Bitvector32Term::Constant(4)),
            ),
        });
    let message = refuse_unproved_conversion_bounds(
        &unproved(Proposition::CMemoryLoadable {
            memory: state.memory().clone(),
            base: indexed_cell(&values),
            bytes: Bitvector32Term::Constant(4),
        }),
        &assumptions,
        &site,
    )
    .expect_err("an unproved mandatory condition is refused");
    assert!(message.starts_with("the expression `index`:"), "{message}");
    assert!(message.contains("premises consulted (2,"), "{message}");
    assert!(message.contains("`0 <= index`"), "{message}");
    // The range premise over the same object is the one a reader believes
    // covers the cell, so the refusal has to name it as consulted.
    assert!(
        message.contains("why that was not enough: `viewable(p[0..index])`"),
        "{message}"
    );
}

/// An overflow guard names the operation it is about, in the spelling the
/// statement uses and without the composing printer's outer parentheses.
#[test]
fn an_overflow_guard_names_its_operation_without_wrapping_parentheses() {
    let (values, state) = indexed_pointer_site();
    let expression = CExpression::Variable("index".to_string());
    let site = StatedSite::new(StatedForm::CFragment(&expression), &state, &values);
    let message = refuse_unproved_conversion_bounds(
        &unproved(Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedSubtractOverflows(
                Box::new(Bitvector32Term::Variable(Variable(1))),
                Box::new(Bitvector32Term::Constant(1)),
            ),
            false,
        )),
        &PureFactContext::new(),
        &site,
    )
    .expect_err("an unproved mandatory condition is refused");
    assert!(
        message.contains("`index - 1` must not overflow"),
        "{message}"
    );
    assert!(message.contains("`defined(index - 1)`"), "{message}");
}

/// A condition the premises do prove is reported as established rather than
/// omitted, so the reader can see what the statement already has.
#[test]
fn established_conditions_are_named_beside_the_missing_one() {
    let (values, state) = indexed_pointer_site();
    let expression = CExpression::Variable("index".to_string());
    let site = StatedSite::new(StatedForm::CFragment(&expression), &state, &values);
    let guard = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedSubtractOverflows(
            Box::new(Bitvector32Term::Variable(Variable(1))),
            Box::new(Bitvector32Term::Constant(1)),
        ),
        false,
    );
    let loadable = Proposition::CMemoryLoadable {
        memory: state.memory().clone(),
        base: indexed_cell(&values),
        bytes: Bitvector32Term::Constant(4),
    };
    let message = refuse_unproved_conversion_bounds(
        &unproved(Proposition::And(
            Box::new(guard.clone()),
            Box::new(loadable),
        )),
        &PureFactContext::new().assume_proposition(guard),
        &site,
    )
    .expect_err("an unproved mandatory condition is refused");
    assert!(
        message.contains("establish 1 of them, not this one"),
        "{message}"
    );
    assert!(
        message.contains("established: `index - 1` must not overflow"),
        "{message}"
    );
    assert!(
        message.contains("not established: the 4 bytes at `p[index]` must be viewable"),
        "{message}"
    );
}

/// Every refusal says why it has no line or column, so a reader stops looking
/// for one.
#[test]
fn every_refusal_says_no_span_is_available() {
    let (values, state) = indexed_pointer_site();
    let expression = CExpression::Variable("index".to_string());
    let site = StatedSite::new(StatedForm::CFragment(&expression), &state, &values);
    let message = refuse_unproved_conversion_bounds(
        &unproved(Proposition::ConditionIs(
            ConditionTerm::Constant(false),
            true,
        )),
        &PureFactContext::new(),
        &site,
    )
    .expect_err("an unproved mandatory condition is refused");
    assert!(
        message.contains("no line or column is available"),
        "{message}"
    );
}

/// An assumable obligation is the evaluation's own consequence, not a
/// condition of it, and is never refused here.
#[test]
fn an_assumable_obligation_is_not_refused() {
    let (values, state) = indexed_pointer_site();
    let expression = CExpression::Variable("index".to_string());
    let site = StatedSite::new(StatedForm::CFragment(&expression), &state, &values);
    let assumable = vec![crate::kernel::ProofObligation::new(
        Proposition::CMemoryLoadable {
            memory: state.memory().clone(),
            base: indexed_cell(&values),
            bytes: Bitvector32Term::Constant(4),
        },
    )];
    assert!(refuse_unproved_conversion_bounds(&assumable, &PureFactContext::new(), &site).is_ok());
}

/// `icount(p, 0, index) == (0..index).fold(0, |acc, k| acc + to_integer(p[k]))`,
/// the defining equation a function `unfold` lowers.
fn fold_defining_equation() -> ClickProposition {
    let read = ContractExpression::ArrayIndex {
        base: Box::new(ContractExpression::CFragment(CExpression::Variable(
            "p".to_string(),
        ))),
        indexes: vec![CExpression::Variable("k".to_string())],
        lowered: CExpression::TypedLoad {
            pointer: Box::new(CExpression::Add(
                Box::new(CExpression::Variable("p".to_string())),
                Box::new(CExpression::Variable("k".to_string())),
            )),
            value_type: CType::Int32,
            volatile: false,
            pointee_constant: false,
            source: Default::default(),
        },
    };
    ClickProposition::Comparison {
        left: ContractExpression::Call {
            name: "icount".to_string(),
            arguments: vec![
                ContractExpression::CFragment(CExpression::Variable("p".to_string())),
                ContractExpression::IntegerLiteral("0".to_string()),
                ContractExpression::CFragment(CExpression::Variable("index".to_string())),
            ],
        },
        operator: ComparisonOperator::Equal,
        right: ContractExpression::RangeFold {
            start: Box::new(ContractExpression::IntegerLiteral("0".to_string())),
            end: Box::new(ContractExpression::CFragment(CExpression::Variable(
                "index".to_string(),
            ))),
            initial: Box::new(ContractExpression::IntegerLiteral("0".to_string())),
            accumulator: "acc".to_string(),
            item: "k".to_string(),
            body: Box::new(ContractExpression::Add(
                Box::new(ContractExpression::Binding("acc".to_string())),
                Box::new(ContractExpression::Call {
                    name: "to_integer".to_string(),
                    arguments: vec![read],
                }),
            )),
        },
    }
}

/// A fold body that evaluated to more than one value: the refusal must name the
/// fold's own binder, the body it could not evaluate once, and the read that
/// body performs, all in the spelling the source uses.
#[test]
fn a_split_fold_body_names_its_binder_its_body_and_its_read() {
    let (values, state) = indexed_pointer_site();
    let proposition = fold_defining_equation();
    let site = StatedSite::new(StatedForm::Proposition(&proposition), &state, &values);
    let message = describe_dropped_fold_body(
        &crate::kernel::DroppedFoldBody {
            body_paths: 2,
            unavailable_body_fact: None,
            item: Variable(1 << 41),
        },
        &PureFactContext::new(),
        &site,
    );
    assert!(message.starts_with("the proposition `"), "{message}");
    assert!(
        message.contains("its subterm `acc + to_integer(p[k])`, the body of the fold over `k`"),
        "{message}"
    );
    assert!(
        message.contains("must denote one value for every `k` in that range"),
        "{message}"
    );
    assert!(
        message.contains("not established: the body evaluated to 2 values, not one"),
        "{message}"
    );
    assert!(
        message.contains("the body reads, once per item: `p[k]`"),
        "{message}"
    );
    assert!(message.contains("premises consulted: none"), "{message}");
    assert!(message.contains("to repair: "), "{message}");
}

/// A fold body that evaluated to one value under a condition on its own item:
/// the refusal must quote that condition and say why a condition raised under
/// the binder is not a fact about this state.
#[test]
fn a_conditional_fold_body_quotes_the_condition_it_carried_out() {
    let (values, state) = indexed_pointer_site();
    let proposition = fold_defining_equation();
    let site = StatedSite::new(StatedForm::Proposition(&proposition), &state, &values);
    let message = describe_dropped_fold_body(
        &crate::kernel::DroppedFoldBody {
            body_paths: 1,
            unavailable_body_fact: Some(Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::Variable(Variable(1 << 41))),
                    Box::new(Bitvector32Term::Variable(Variable(1))),
                ),
                true,
            )),
            item: Variable(1 << 41),
        },
        &PureFactContext::new(),
        &site,
    );
    assert!(
        message.contains(
            "not established: the body evaluated to one value, but carried the \
                          condition `"
        ),
        "{message}"
    );
    assert!(
        message.contains("A condition raised under the fold's binders is about which `k` this is"),
        "{message}"
    );
}

#[test]
fn one_outer_parenthesis_pair_is_dropped_and_a_composed_one_is_kept() {
    let sum = ContractExpression::CFragment(CExpression::Add(
        Box::new(CExpression::Variable("a".to_string())),
        Box::new(CExpression::Variable("b".to_string())),
    ));
    assert_eq!(spelled_alone(&sum), "a + b");
    let nested = ContractExpression::CFragment(CExpression::Add(
        Box::new(CExpression::Add(
            Box::new(CExpression::Variable("a".to_string())),
            Box::new(CExpression::Variable("b".to_string())),
        )),
        Box::new(CExpression::Add(
            Box::new(CExpression::Variable("c".to_string())),
            Box::new(CExpression::Variable("d".to_string())),
        )),
    ));
    assert_eq!(spelled_alone(&nested), "(a + b) + (c + d)");
    let bare = ContractExpression::CFragment(CExpression::Variable("a".to_string()));
    assert_eq!(spelled_alone(&bare), "a");
}
