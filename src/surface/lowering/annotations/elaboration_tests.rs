//! Elaboration from declared types alone (`design/typed-surface.md`).
//!
//! Each test builds an `Elaborator` from declarations and a typing
//! environment over `NoOuterNames`, with no lowerer and no lowering context,
//! and checks the Surface it gives. The declarations hold no kernel state.
use super::typing_environment::NoOuterNames;
use super::*;
use crate::surface::typed_surface::{
    ArithmeticKind, ArithmeticOperator, ComparisonKind, LeafType, Quantifier,
};

/// Click binders with their declared types, and C parameters with theirs.
struct Declared {
    binders: Vec<(&'static str, ClickType)>,
    c_parameters: Vec<(&'static str, ProgramType)>,
}

/// A pointer parameter's declared element: its type and its width.
type PointerElementDeclaration = (&'static str, ProgramType, u32);

impl Declared {
    fn elaborate<'s>(&self, proposition: &'s SyntaxProposition) -> SurfaceProposition<'s> {
        self.run(|elaborator, typing| elaborator.elaborate_proposition(proposition, typing))
    }

    fn elaborate_clause<'s>(&self, proposition: &'s SyntaxProposition) -> SurfaceProposition<'s> {
        self.run(|elaborator, typing| elaborator.elaborate_clause(proposition, typing))
    }

    fn elaborate_comparison(
        &self,
        left: SyntaxTerm,
        operator: ComparisonOperator,
        right: SyntaxTerm,
    ) -> Result<SurfaceProposition<'static>, String> {
        self.run(|elaborator, typing| {
            elaborator.elaborate_comparison(&left, operator, &right, typing)
        })
    }

    fn run<T>(&self, elaborate: impl FnOnce(&Elaborator<'_>, &TypingEnvironment<'_>) -> T) -> T {
        self.run_with_pointer_elements(&[], elaborate)
    }

    fn run_with_pointer_elements<T>(
        &self,
        pointer_elements: &[PointerElementDeclaration],
        elaborate: impl FnOnce(&Elaborator<'_>, &TypingEnvironment<'_>) -> T,
    ) -> T {
        let predicates = PredicateEnvironment::new(&[]);
        let functions = ClickFunctionEnvironment::new(&[]);
        let elaborator = Elaborator {
            declarations: Declarations {
                source_bindings: None,
                entry_state: None,
                result_type: ProgramType::Int32,
                entry_values: Default::default(),
                local_type_state: None,
                global_declarations: None,
                program_parameter_types: Arc::new(
                    self.c_parameters
                        .iter()
                        .map(|(name, ty)| (name.to_string(), *ty))
                        .collect(),
                ),
                pointer_element_types: Arc::new(
                    pointer_elements
                        .iter()
                        .map(|(name, element, _)| (name.to_string(), *element))
                        .collect(),
                ),
                parameter_pointer_element_widths: Arc::new(
                    pointer_elements
                        .iter()
                        .map(|(name, _, width)| (name.to_string(), *width))
                        .collect(),
                ),
                spelled_local_types: Default::default(),
            },
            definitions: SpecDefinitions::new(&predicates, &functions),
            retained_states: None,
            capture_referenced_names: None,
            type_inference_failure: Default::default(),
        };
        let mut typing = TypingEnvironment::in_scope(&NoOuterNames);
        for (name, declared) in &self.binders {
            typing.declare(*name, declared.clone());
        }
        elaborate(&elaborator, &typing)
    }
}

fn binder(name: &str) -> SyntaxTerm {
    SyntaxTerm::Binding(name.into())
}

fn c_variable(name: &str) -> SyntaxTerm {
    SyntaxTerm::ProgramExpression(ProgramExpression::Variable(name.into()))
}

fn literal(text: &str) -> SyntaxTerm {
    SyntaxTerm::IntegerLiteral(text.into())
}

fn integer_name(name: &str) -> SurfaceTerm {
    SurfaceTerm::Name {
        name: name.into(),
        ty: LeafType::Integer,
    }
}

fn program_literal(text: &str, ty: ProgramType) -> SurfaceTerm {
    SurfaceTerm::IntegerLiteral {
        text: text.into(),
        ty: LeafType::Program(ty),
    }
}

#[test]
fn integer_binders_elaborate_to_an_integer_comparison_of_integer_arithmetic() {
    let declared = Declared {
        binders: vec![("n", ClickType::Integer), ("m", ClickType::Integer)],
        c_parameters: vec![],
    };
    let surface = declared.elaborate_comparison(
        SyntaxTerm::Add(Box::new(binder("n")), Box::new(literal("1"))),
        ComparisonOperator::LessEqual,
        binder("m"),
    );
    assert_eq!(
        surface,
        Ok(SurfaceProposition::Comparison {
            kind: ComparisonKind::Integer,
            left: SurfaceTerm::Binary {
                op: ArithmeticOperator::Add,
                kind: ArithmeticKind::Integer,
                left: Box::new(integer_name("n")),
                right: Box::new(SurfaceTerm::IntegerLiteral {
                    text: "1".into(),
                    ty: LeafType::Integer,
                }),
            },
            operator: ComparisonOperator::LessEqual,
            right: integer_name("m"),
        })
    );
}

#[test]
fn c_parameters_elaborate_to_a_native_comparison_at_their_declared_types() {
    let declared = Declared {
        binders: vec![],
        c_parameters: vec![("x", ProgramType::Int32), ("y", ProgramType::Int64)],
    };
    let surface = declared.elaborate_comparison(
        SyntaxTerm::Multiply(Box::new(c_variable("x")), Box::new(literal("2"))),
        ComparisonOperator::Equal,
        literal("6"),
    );
    assert_eq!(
        surface,
        Ok(SurfaceProposition::Comparison {
            kind: ComparisonKind::Native,
            left: SurfaceTerm::Binary {
                op: ArithmeticOperator::Multiply,
                kind: ArithmeticKind::Native,
                left: Box::new(SurfaceTerm::Name {
                    name: "x".into(),
                    ty: LeafType::Program(ProgramType::Int32),
                }),
                right: Box::new(program_literal("2", ProgramType::Int32)),
            },
            operator: ComparisonOperator::Equal,
            right: program_literal("6", ProgramType::Int32),
        })
    );
    // C types an unsuffixed constant by its value: one past `int32` is an
    // `int64`.
    let surface = declared.elaborate_comparison(
        c_variable("y"),
        ComparisonOperator::LessThan,
        literal("3000000000"),
    );
    assert_eq!(
        surface,
        Ok(SurfaceProposition::Comparison {
            kind: ComparisonKind::Native,
            left: SurfaceTerm::Name {
                name: "y".into(),
                ty: LeafType::Program(ProgramType::Int64),
            },
            operator: ComparisonOperator::LessThan,
            right: program_literal("3000000000", ProgramType::Int64),
        })
    );
}

#[test]
fn an_integer_binder_compared_with_a_c_value_is_refused() {
    let declared = Declared {
        binders: vec![("n", ClickType::Integer)],
        c_parameters: vec![("x", ProgramType::Int32)],
    };
    assert_eq!(
        declared.elaborate_comparison(binder("n"), ComparisonOperator::Equal, c_variable("x")),
        Err("mathematical Integer expressions cannot be compared with C values".to_string())
    );
}

#[test]
fn algebraic_binders_elaborate_to_an_algebraic_equality_and_refuse_ordering() {
    let list = ClickType::Algebraic(AlgebraicTypeApplication::concrete("List"));
    let declared = Declared {
        binders: vec![("a", list.clone()), ("b", list)],
        c_parameters: vec![],
    };
    assert_eq!(
        declared.elaborate_comparison(binder("a"), ComparisonOperator::Equal, binder("b")),
        Ok(SurfaceProposition::Comparison {
            kind: ComparisonKind::Algebraic,
            left: SurfaceTerm::Untyped(binder("a")),
            operator: ComparisonOperator::Equal,
            right: SurfaceTerm::Untyped(binder("b")),
        })
    );
    assert_eq!(
        declared.elaborate_comparison(binder("a"), ComparisonOperator::LessThan, binder("b")),
        Err("algebraic values support only `==` and `!=` comparisons".to_string())
    );
}

#[test]
fn connectives_elaborate_around_each_comparison_and_a_refused_one_stays_untyped() {
    let declared = Declared {
        binders: vec![("n", ClickType::Integer)],
        c_parameters: vec![("x", ProgramType::Int32)],
    };
    let refused = SyntaxProposition::Comparison {
        left: binder("n"),
        operator: ComparisonOperator::Equal,
        right: c_variable("x"),
    };
    let proposition = SyntaxProposition::And(
        Box::new(SyntaxProposition::Comparison {
            left: binder("n"),
            operator: ComparisonOperator::GreaterThan,
            right: literal("0"),
        }),
        Box::new(SyntaxProposition::Not(Box::new(refused.clone()))),
    );
    let SurfaceProposition::And(left, right) = declared.elaborate(&proposition) else {
        panic!("a conjunction elaborates to a conjunction");
    };
    assert_eq!(
        *left,
        SurfaceProposition::Comparison {
            kind: ComparisonKind::Integer,
            left: integer_name("n"),
            operator: ComparisonOperator::GreaterThan,
            right: SurfaceTerm::IntegerLiteral {
                text: "0".into(),
                ty: LeafType::Integer,
            },
        }
    );
    // Lowering reaches the refused comparison and reports its error there.
    assert_eq!(
        *right,
        SurfaceProposition::Not(Box::new(SurfaceProposition::Untyped(&refused)))
    );
}

#[test]
fn a_step_through_an_untyped_pointer_parameter_stays_untyped_for_lowering_to_refuse() {
    // Elaboration refuses `p - 1` for a `Pointer` `p` from its declared type
    // alone: the step has no pointee type, so it stays `Untyped` and lowering
    // reports the refusal where it reaches it.
    let declared = Declared {
        binders: vec![],
        c_parameters: vec![("p", ProgramType::Pointer)],
    };
    let step = SyntaxTerm::Subtract(Box::new(c_variable("p")), Box::new(literal("1")));
    let Ok(SurfaceProposition::Comparison { kind, left, .. }) =
        declared.elaborate_comparison(step.clone(), ComparisonOperator::Equal, c_variable("p"))
    else {
        panic!("a pointer comparison elaborates to a comparison");
    };
    assert_eq!(kind, ComparisonKind::Native);
    assert_eq!(left, SurfaceTerm::Untyped(step));
}

#[test]
fn a_step_of_a_pointer_parameter_is_a_pointer_step_by_its_declared_element_width() {
    // `p + 1` for an `int32 *` parameter steps by the declared 4-byte
    // element, decided by elaboration from the declaration with no lowerer.
    let declared = Declared {
        binders: vec![],
        c_parameters: vec![("p", ProgramType::Int32Pointer)],
    };
    let step = SyntaxTerm::Add(Box::new(c_variable("p")), Box::new(literal("1")));
    let surface = declared.run_with_pointer_elements(
        &[("p", ProgramType::Int32, 4)],
        |elaborator, typing| {
            elaborator.elaborate_comparison(
                &step,
                ComparisonOperator::Equal,
                &c_variable("p"),
                typing,
            )
        },
    );
    let Ok(SurfaceProposition::Comparison { kind, left, .. }) = surface else {
        panic!("a pointer comparison elaborates to a comparison");
    };
    assert_eq!(kind, ComparisonKind::Native);
    assert_eq!(
        left,
        SurfaceTerm::PointerStep {
            pointer: Box::new(SurfaceTerm::Name {
                name: "p".into(),
                ty: LeafType::Program(ProgramType::Int32Pointer),
            }),
            elements: Box::new(program_literal("1", ProgramType::Int32)),
            element_width: 4,
            backward: false,
        }
    );
}

#[test]
fn a_quantifier_body_elaborates_with_its_binder_declared() {
    // `forall i: Integer. i + 1 > i` with no outer names: the body's
    // comparison is an Integer comparison because the binder is declared an
    // Integer, not because lowering bound it.
    let declared = Declared {
        binders: vec![],
        c_parameters: vec![],
    };
    let body = SyntaxProposition::Comparison {
        left: SyntaxTerm::Add(Box::new(binder("i")), Box::new(literal("1"))),
        operator: ComparisonOperator::GreaterThan,
        right: binder("i"),
    };
    let quantifier = SyntaxProposition::ForAll {
        click_type: ClickType::Integer,
        name: "i".into(),
        written_name: None,
        body: Box::new(body),
    };
    let SurfaceProposition::Quantified {
        quantifier: Quantifier::All,
        name,
        click_type,
        body,
        ..
    } = declared.elaborate_clause(&quantifier)
    else {
        panic!("a quantifier elaborates to a quantified Surface proposition");
    };
    assert_eq!(name, SurfaceBinder::from("i"));
    assert_eq!(click_type, ClickType::Integer);
    let SurfaceProposition::Comparison { kind, right, .. } = *body else {
        panic!("the body elaborates to a comparison");
    };
    assert_eq!(kind, ComparisonKind::Integer);
    assert_eq!(right, integer_name("i"));
    // The connective-only elaboration leaves the quantifier for lowering.
    assert_eq!(
        declared.elaborate(&quantifier),
        SurfaceProposition::Untyped(&quantifier)
    );
}

#[test]
fn a_range_with_a_uint64_endpoint_ranges_over_uint64() {
    // `forall k in 0..n` for a `uint64` parameter `n`: the item is a
    // `uint64`, as lowering binds it, and the body sees it at that type.
    let declared = Declared {
        binders: vec![],
        c_parameters: vec![("n", ProgramType::UInt64)],
    };
    let range = SyntaxProposition::RangeAll {
        start: literal("0"),
        end: c_variable("n"),
        item: "k".into(),
        written_item: None,
        body: Box::new(SyntaxProposition::Comparison {
            left: c_variable("k"),
            operator: ComparisonOperator::LessThan,
            right: c_variable("n"),
        }),
    };
    let SurfaceProposition::Range {
        quantifier: Quantifier::All,
        item_type,
        body,
        ..
    } = declared.elaborate_clause(&range)
    else {
        panic!("a range elaborates to a range Surface proposition");
    };
    assert_eq!(item_type, ProgramType::UInt64);
    let SurfaceProposition::Comparison { kind, left, .. } = *body else {
        panic!("the body elaborates to a comparison");
    };
    assert_eq!(kind, ComparisonKind::Native);
    // A binder spelled as a C name is not a declared C variable, so the
    // native operand stays `Untyped`, as lowering's own elaboration leaves it.
    assert_eq!(left, SurfaceTerm::Untyped(c_variable("k")));
}
