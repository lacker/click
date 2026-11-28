//! Elaborating and lowering a written comparison.
//!
//! Elaboration chooses the comparison's kind from both operands
//! (`design/typed-surface.md`); lowering then reads the kind and lowers each
//! operand the way the kind says, without inspecting the operands again.
use super::*;

impl AnnotationLowerer<'_> {
    /// Elaborate `left operator right` in the lowering context it is lowered
    /// in.
    pub(super) fn elaborate_comparison(
        &mut self,
        left: &SyntaxTerm,
        operator: ComparisonOperator,
        right: &SyntaxTerm,
        environment: &SpecElaborationContext,
    ) -> Result<SurfaceProposition<'static>, String> {
        self.with_elaborator(|elaborator| {
            elaborator.elaborate_comparison(
                left,
                operator,
                right,
                &TypingEnvironment::of(environment),
            )
        })
    }
}

impl Elaborator<'_> {
    /// Elaborate a proposition to Surface in the lowering context it is
    /// lowered in: its connectives, and each comparison directly under them
    /// with its kind. A comparison whose elaboration fails stays `Untyped`,
    /// so lowering reaches it where it did before and reports the same error
    /// in the same order. Connectives do not change the context, so each
    /// comparison is elaborated in the context lowering would use for it.
    pub(super) fn elaborate_proposition<'s>(
        &self,
        proposition: &'s SyntaxProposition,
        typing: &TypingEnvironment<'_>,
    ) -> SurfaceProposition<'s> {
        let mut surface = crate::surface::elaborate_connectives(proposition);
        let mut pending = vec![&mut surface];
        while let Some(node) = pending.pop() {
            match node {
                SurfaceProposition::And(left, right)
                | SurfaceProposition::Or(left, right)
                | SurfaceProposition::Implies(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                SurfaceProposition::Not(body) => pending.push(body),
                SurfaceProposition::Untyped(SyntaxProposition::Comparison {
                    left,
                    operator,
                    right,
                }) => {
                    if let Ok(comparison) =
                        self.elaborate_comparison(left, *operator, right, typing)
                    {
                        *node = comparison;
                    }
                }
                _ => {}
            }
        }
        surface
    }

    /// The slice type of a comparison operand that reads a program slice,
    /// `s`, `old(s)` or `at(p, s)`; `None` for any other operand.
    fn comparison_slice_type(
        &self,
        term: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
    ) -> Option<ProgramType> {
        match term {
            SyntaxTerm::ProgramExpression(expression) => {
                self.declarations.slice_expression_type(expression, typing)
            }
            SyntaxTerm::Old(inner) => self.comparison_slice_type(inner, typing),
            SyntaxTerm::At { expression, .. } => self.comparison_slice_type(expression, typing),
            _ => None,
        }
    }

    /// The typed Surface form of `left operator right`.
    pub(super) fn elaborate_comparison(
        &self,
        left: &SyntaxTerm,
        operator: ComparisonOperator,
        right: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
    ) -> Result<SurfaceProposition<'static>, String> {
        let comparison = |kind| {
            Ok(SurfaceProposition::Comparison {
                kind,
                left: SurfaceTerm::Untyped(left.clone()),
                operator,
                right: SurfaceTerm::Untyped(right.clone()),
            })
        };
        // A slice is one value, not its data pointer: a slice compared with
        // a thin pointer is written on `s.as_ptr()`
        // (`design/rust-slice-values.md`, "Source compatibility").
        for (slice, other) in [(left, right), (right, left)] {
            if self.comparison_slice_type(slice, typing).is_some()
                && self.comparison_slice_type(other, typing).is_none()
                && self.contract_pointer_element_type(other, typing).is_some()
            {
                let written = crate::surface::diagnostics::describe_contract_expression(slice);
                return Err(format!(
                    "`{written}` is a slice, not a pointer: a pointer comparison is written on its data pointer, `.as_ptr()`, as in `{written}.as_ptr() == p`"
                ));
            }
        }
        if let (Some(left_element), Some(right_element)) = (
            self.contract_pointer_element_type(left, typing),
            self.contract_pointer_element_type(right, typing),
        ) && left_element != right_element
        {
            return Err(format!(
                "incompatible pointer comparison: {:?} pointer and {:?} pointer; use a checked byte-view cast to compare byte views",
                left_element, right_element
            ));
        }
        if operator == ComparisonOperator::In {
            return comparison(ComparisonKind::Sequence);
        }
        let left_is_integer = self.contract_expression_is_integer(left, typing);
        let right_is_integer = self.contract_expression_is_integer(right, typing);
        let left_is_integer = left_is_integer
            || (right_is_integer && matches!(left, SyntaxTerm::AlgebraicMatch { .. }));
        let right_is_integer = right_is_integer
            || (left_is_integer && matches!(right, SyntaxTerm::AlgebraicMatch { .. }));
        if left_is_integer || right_is_integer {
            if left_is_integer != right_is_integer
                && !(if left_is_integer {
                    is_unsuffixed_integer_literal_expression(right)
                } else {
                    is_unsuffixed_integer_literal_expression(left)
                })
            {
                return Err(
                    "mathematical Integer expressions cannot be compared with C values".to_string(),
                );
            }
            return Ok(SurfaceProposition::Comparison {
                kind: ComparisonKind::Integer,
                left: integer_surface_term(left.clone(), typing),
                operator,
                right: integer_surface_term(right.clone(), typing),
            });
        }
        // Two values of one struct are equal when each field is: the
        // constructor is injective, so the comparison is its fields'.
        if matches!(
            operator,
            ComparisonOperator::Equal | ComparisonOperator::NotEqual
        ) && let (Some((left_type, left_fields)), Some((right_type, right_fields))) = (
            struct_constructor_fields(left),
            struct_constructor_fields(right),
        ) && left_type == right_type
            && left_fields.len() == right_fields.len()
            && !left_fields.is_empty()
            && crate::surface::struct_values::field_names(&left_type).is_some()
        {
            let mut fields = None;
            for (left, right) in left_fields.iter().zip(&right_fields) {
                let field =
                    self.elaborate_comparison(left, ComparisonOperator::Equal, right, typing)?;
                fields = Some(match fields {
                    None => field,
                    Some(before) => SurfaceProposition::And(Box::new(before), Box::new(field)),
                });
            }
            let equal = fields.expect("a struct value has a field");
            return Ok(if operator == ComparisonOperator::Equal {
                equal
            } else {
                SurfaceProposition::Not(Box::new(equal))
            });
        }
        let has_algebraic = self.enum_program_value_type(left, typing).is_some()
            || self.enum_program_value_type(right, typing).is_some()
            || contract_expression_is_algebraic(
                left,
                self.definitions.functions,
                typing,
                &mut Vec::new(),
            )
            || contract_expression_is_algebraic(
                right,
                self.definitions.functions,
                typing,
                &mut Vec::new(),
            )
            || self.generic_call_returns_algebraic(left, typing)
            || self.generic_call_returns_algebraic(right, typing);
        let equality_only = |kind, message: &str| {
            if matches!(
                operator,
                ComparisonOperator::Equal | ComparisonOperator::NotEqual
            ) {
                comparison(kind)
            } else {
                Err(message.to_string())
            }
        };
        if has_algebraic {
            return equality_only(
                ComparisonKind::Algebraic,
                "algebraic values support only `==` and `!=` comparisons",
            );
        }
        if contract_expression_is_sequence(left) || contract_expression_is_sequence(right) {
            return equality_only(
                ComparisonKind::Sequence,
                "sequences support only `==` and `!=` comparisons",
            );
        }
        Ok(SurfaceProposition::Comparison {
            kind: ComparisonKind::Native,
            left: self.native_surface_term(left.clone(), typing),
            operator,
            right: self.native_surface_term(right.clone(), typing),
        })
    }
}

impl AnnotationLowerer<'_> {
    /// Lower a Surface proposition. Connectives are lowered here, each over
    /// its operands' lowerings; a comparison by its elaborated kind; an
    /// `Untyped` construct by the Syntax lowering it had before it moved to
    /// Surface. Iterative, so a long chain needs no deep stack.
    pub(super) fn lower_surface_proposition(
        &mut self,
        proposition: &SurfaceProposition<'_>,
        environment: &SpecElaborationContext,
    ) -> Result<SpecProposition, String> {
        enum Frame<'p, 's> {
            Visit(&'p SurfaceProposition<'s>),
            BuildAnd,
            BuildOr,
            BuildImplies,
            BuildNot,
        }
        let mut frames = vec![Frame::Visit(proposition)];
        let mut lowered = Vec::new();
        while let Some(frame) = frames.pop() {
            let visit = match frame {
                Frame::Visit(visit) => visit,
                Frame::BuildNot => {
                    let body = lowered.pop().expect("lowered negation body");
                    lowered.push(SpecProposition::Not(Box::new(body)));
                    continue;
                }
                frame => {
                    let right = Box::new(lowered.pop().expect("lowered right operand"));
                    let left = Box::new(lowered.pop().expect("lowered left operand"));
                    lowered.push(match frame {
                        Frame::BuildAnd => SpecProposition::And(left, right),
                        Frame::BuildOr => SpecProposition::Or(left, right),
                        _ => SpecProposition::Implies(left, right),
                    });
                    continue;
                }
            };
            // One visit per node: a connective, an elaborated comparison, or
            // an untyped construct.
            #[cfg(test)]
            super::tests::PROPOSITION_VISITS.with(|visits| visits.set(visits.get() + 1));
            match visit {
                SurfaceProposition::And(left, right) => {
                    frames.extend([Frame::BuildAnd, Frame::Visit(right), Frame::Visit(left)]);
                }
                SurfaceProposition::Or(left, right) => {
                    frames.extend([Frame::BuildOr, Frame::Visit(right), Frame::Visit(left)]);
                }
                SurfaceProposition::Implies(left, right) => {
                    frames.extend([Frame::BuildImplies, Frame::Visit(right), Frame::Visit(left)]);
                }
                SurfaceProposition::Not(body) => {
                    frames.extend([Frame::BuildNot, Frame::Visit(body)]);
                }
                SurfaceProposition::Untyped(syntax) => {
                    lowered
                        .push(self.click_proposition_to_spec_proposition_one(syntax, environment)?);
                }
                // A binder form binds as written and lowers the body
                // elaboration gave it.
                SurfaceProposition::Quantified { syntax, body, .. }
                | SurfaceProposition::Range { syntax, body, .. } => {
                    lowered.push(self.lower_elaborated_binder(syntax, body, environment)?);
                }
                SurfaceProposition::Comparison {
                    kind,
                    left,
                    operator,
                    right,
                } => {
                    lowered.push(self.lower_surface_comparison(
                        *kind,
                        left,
                        *operator,
                        right,
                        environment,
                    )?);
                }
            }
        }
        Ok(lowered.pop().expect("lowered proposition has one root"))
    }

    /// Lower a native Surface term. A native operation is lowered as
    /// `lower_contract_expression_to_spec` lowers its Syntax form: the
    /// operator's Spec node over its operands' lowerings. Nothing before
    /// those arms applies to these operators: they are never pointer
    /// arithmetic, never refused as untyped pointer access, and never a
    /// region read. An `Untyped` term is lowered by that Syntax lowering.
    fn lower_surface_native(
        &mut self,
        term: &SurfaceTerm,
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        use ArithmeticOperator as Op;
        match term {
            SurfaceTerm::Untyped(syntax) => {
                self.lower_contract_expression_to_spec(syntax, environment)
            }
            SurfaceTerm::IntegerLiteral {
                text,
                ty: LeafType::Program(ty),
            } => {
                let value: u64 = text
                    .parse()
                    .expect("a native literal elaborates only from a u64 value");
                Ok(SpecExpression::Value(match ty {
                    ProgramType::Int32 => {
                        ProgramValue::Int32(OldMachineTerm::constant(value as u32))
                    }
                    ProgramType::Int64 => {
                        ProgramValue::Int64(OldMachineTerm::int64_constant(value as i64))
                    }
                    _ => ProgramValue::UInt64(OldMachineTerm::uint64_constant(value)),
                }))
            }
            // A C variable is resolved at the program point exactly as the
            // Syntax lowering resolved it.
            SurfaceTerm::Name {
                name,
                ty: LeafType::Program(_),
            } => self.lower_program_expression_to_spec(
                &ProgramExpression::Variable(crate::kernel::BindingName::Named(name.clone())),
                environment,
            ),
            SurfaceTerm::IntegerLiteral {
                ty: LeafType::Integer,
                ..
            }
            | SurfaceTerm::Name {
                ty: LeafType::Integer,
                ..
            } => {
                unreachable!("a native operand is never an Integer literal or binder: {term:?}")
            }
            SurfaceTerm::BitwiseNot { operand } => Ok(SpecExpression::BitwiseNot(Box::new(
                self.lower_surface_native(operand, environment)?,
            ))),
            // As the Syntax lowering builds a pointer step: `p - k` moves
            // by `0 - k` elements.
            SurfaceTerm::PointerStep {
                pointer,
                elements,
                element_width,
                backward,
            } => {
                let pointer = Box::new(self.lower_surface_native(pointer, environment)?);
                let elements = self.lower_surface_native(elements, environment)?;
                let elements = if *backward {
                    SpecExpression::Subtract(
                        Box::new(SpecExpression::Value(int32(0))),
                        Box::new(elements),
                    )
                } else {
                    elements
                };
                Ok(SpecExpression::PointerOffset {
                    pointer,
                    elements: Box::new(elements),
                    byte_width: *element_width,
                })
            }
            SurfaceTerm::Binary {
                op,
                kind: ArithmeticKind::Native,
                left,
                right,
            } => {
                let left = Box::new(self.lower_surface_native(left, environment)?);
                let right = Box::new(self.lower_surface_native(right, environment)?);
                Ok(match op {
                    Op::Multiply => SpecExpression::Multiply(left, right),
                    Op::Divide => SpecExpression::Divide(left, right),
                    Op::Remainder => SpecExpression::Remainder(left, right),
                    Op::ShiftLeft => SpecExpression::ShiftLeft(left, right),
                    Op::RustShiftLeft => SpecExpression::RustShiftLeft(left, right),
                    Op::ShiftRight => SpecExpression::ShiftRight(left, right),
                    Op::RustShiftRight => SpecExpression::RustShiftRight(left, right),
                    Op::BitwiseAnd => SpecExpression::BitwiseAnd(left, right),
                    Op::BitwiseOr => SpecExpression::BitwiseOr(left, right),
                    Op::BitwiseXor => SpecExpression::BitwiseXor(left, right),
                    Op::Subtract => SpecExpression::Subtract(left, right),
                    Op::Add => SpecExpression::Add(left, right),
                })
            }
            SurfaceTerm::Negate {
                kind: ArithmeticKind::Native,
                operand,
            } => Ok(SpecExpression::Negate(Box::new(
                self.lower_surface_native(operand, environment)?,
            ))),
            SurfaceTerm::Binary {
                kind: ArithmeticKind::Integer,
                ..
            }
            | SurfaceTerm::Negate {
                kind: ArithmeticKind::Integer,
                ..
            } => unreachable!("a native operand is never Integer arithmetic: {term:?}"),
        }
    }

    /// Lower an Integer Surface term. Integer arithmetic is lowered as
    /// `lower_contract_integer_to_spec` lowers it: one unit of integer work,
    /// then the operands, combined over Integer terms when both are terms.
    /// An `Untyped` term is lowered by that Syntax lowering.
    fn lower_surface_integer(
        &mut self,
        term: &SurfaceTerm,
        environment: &SpecElaborationContext,
    ) -> Result<crate::kernel::SpecIntegerExpression, String> {
        use crate::kernel::SpecIntegerExpression;
        match term {
            SurfaceTerm::Untyped(syntax) => {
                self.lower_contract_integer_to_spec(syntax, environment)
            }
            // As the Syntax lowering reaches a literal: one unit of integer
            // work, then the shared literal lowering.
            SurfaceTerm::IntegerLiteral {
                text,
                ty: LeafType::Integer,
            } => {
                check_integer_lowering_work(1)?;
                lower_contract_integer_to_spec(
                    &SyntaxTerm::IntegerLiteral(text.clone()),
                    &environment.integer_values,
                )
            }
            // As the Syntax lowering reads a written binder: one unit of
            // integer work, then the Integer binding or the same refusal.
            SurfaceTerm::Name {
                name,
                ty: LeafType::Integer,
            } => {
                check_integer_lowering_work(1)?;
                let value = environment
                    .integer_values
                    .get(name)
                    .ok_or_else(|| format!("`{name}` is not an Integer binding"))?;
                if let SpecIntegerExpression::Term(term) = value {
                    check_integer_lowering_work(integer_root_work(term))?;
                }
                Ok(value.clone())
            }
            SurfaceTerm::Name {
                ty: LeafType::Program(_),
                ..
            }
            | SurfaceTerm::IntegerLiteral {
                ty: LeafType::Program(_),
                ..
            }
            | SurfaceTerm::BitwiseNot { .. }
            | SurfaceTerm::PointerStep { .. }
            | SurfaceTerm::Negate {
                kind: ArithmeticKind::Native,
                ..
            }
            | SurfaceTerm::Binary {
                kind: ArithmeticKind::Native,
                ..
            } => unreachable!("an Integer operand is never native arithmetic: {term:?}"),
            SurfaceTerm::Negate {
                kind: ArithmeticKind::Integer,
                operand,
            } => {
                check_integer_lowering_work(1)?;
                match self.lower_surface_integer(operand, environment)? {
                    SpecIntegerExpression::Term(term) => {
                        check_integer_lowering_work(integer_root_work(&term))?;
                        construct_integer_operation(
                            crate::kernel::KernelIntegerOperator::Negate,
                            vec![term],
                        )
                    }
                    inner => Ok(SpecIntegerExpression::Negate(Box::new(inner))),
                }
            }
            SurfaceTerm::Binary {
                op,
                kind: ArithmeticKind::Integer,
                left,
                right,
            } => {
                check_integer_lowering_work(1)?;
                let left = self.lower_surface_integer(left, environment)?;
                let right = self.lower_surface_integer(right, environment)?;
                let operation = match op {
                    ArithmeticOperator::Add => IntegerOperation::Add,
                    ArithmeticOperator::Subtract => IntegerOperation::Subtract,
                    ArithmeticOperator::Multiply => IntegerOperation::Multiply,
                    other => unreachable!("elaboration types only + - * as Integer: {other:?}"),
                };
                match (&left, &right) {
                    (SpecIntegerExpression::Term(_), SpecIntegerExpression::Term(_)) => {
                        lower_integer_operation(left, right, operation)
                    }
                    _ => Ok(match operation {
                        IntegerOperation::Add => {
                            SpecIntegerExpression::Add(Box::new(left), Box::new(right))
                        }
                        IntegerOperation::Subtract => {
                            SpecIntegerExpression::Subtract(Box::new(left), Box::new(right))
                        }
                        IntegerOperation::Multiply => {
                            SpecIntegerExpression::Multiply(Box::new(left), Box::new(right))
                        }
                    }),
                }
            }
        }
    }

    /// Lower an elaborated comparison. Each operand is lowered as its
    /// comparison's kind says; nothing here looks at the operands to decide.
    fn lower_surface_comparison(
        &mut self,
        kind: ComparisonKind,
        left: &SurfaceTerm,
        operator: ComparisonOperator,
        right: &SurfaceTerm,
        environment: &SpecElaborationContext,
    ) -> Result<SpecProposition, String> {
        if kind == ComparisonKind::Native {
            return Ok(SpecProposition::Comparison {
                left: self.lower_surface_native(left, environment)?,
                operator: c_comparison_operator(operator),
                right: self.lower_surface_native(right, environment)?,
            });
        }
        if kind == ComparisonKind::Integer {
            return Ok(SpecProposition::IntegerComparison {
                left: self.lower_surface_integer(left, environment)?,
                operator: integer_comparison_operator(operator)?,
                right: self.lower_surface_integer(right, environment)?,
            });
        }
        let (left, right) = (left.untyped_syntax(), right.untyped_syntax());
        let equal = operator == ComparisonOperator::Equal;
        match kind {
            ComparisonKind::Integer => unreachable!("lowered above"),
            ComparisonKind::Algebraic => Ok(SpecProposition::AlgebraicComparison {
                left: self.lower_contract_algebraic_to_spec(left, environment)?,
                equal,
                right: self.lower_contract_algebraic_to_spec(right, environment)?,
            }),
            ComparisonKind::Sequence if operator == ComparisonOperator::In => {
                Ok(SpecProposition::SequenceMembership {
                    element: self.lower_contract_expression_to_spec(left, environment)?,
                    sequence: self.lower_contract_sequence_to_spec(right, environment)?,
                })
            }
            ComparisonKind::Sequence => Ok(SpecProposition::SequenceComparison {
                left: self.lower_contract_sequence_to_spec(left, environment)?,
                equal,
                right: self.lower_contract_sequence_to_spec(right, environment)?,
            }),
            ComparisonKind::Native => unreachable!("lowered above"),
        }
    }
}

/// The Integer Surface form of an operand of an Integer comparison: its `+`,
/// `-`, `*` and negation are Integer arithmetic, and every other construct
/// stays `Untyped`. A negated literal stays `Untyped`: lowering reads it as
/// the literal `-n`, not as a negation.
fn integer_surface_term(term: SyntaxTerm, typing: &TypingEnvironment<'_>) -> SurfaceTerm {
    let binary = |op, left: Box<SyntaxTerm>, right: Box<SyntaxTerm>| SurfaceTerm::Binary {
        op,
        kind: ArithmeticKind::Integer,
        left: Box::new(integer_surface_term(*left, typing)),
        right: Box::new(integer_surface_term(*right, typing)),
    };
    if matches!(term, SyntaxTerm::Negate(_)) && integer_literal_spelling(&term).is_some() {
        return SurfaceTerm::Untyped(term);
    }
    match term {
        SyntaxTerm::Add(left, right) => binary(ArithmeticOperator::Add, left, right),
        SyntaxTerm::Subtract(left, right) => binary(ArithmeticOperator::Subtract, left, right),
        SyntaxTerm::Multiply(left, right) => binary(ArithmeticOperator::Multiply, left, right),
        SyntaxTerm::Negate(operand) => SurfaceTerm::Negate {
            kind: ArithmeticKind::Integer,
            operand: Box::new(integer_surface_term(*operand, typing)),
        },
        SyntaxTerm::IntegerLiteral(text) => SurfaceTerm::IntegerLiteral {
            text,
            ty: LeafType::Integer,
        },
        // A Click binder of an Integer comparison is an Integer binder:
        // lowering reads it among the Integer bindings or refuses it.
        // (A generated binder is never a `Binding`.)
        SyntaxTerm::Binding(name) => SurfaceTerm::Name {
            name,
            ty: LeafType::Integer,
        },
        // A C-variable spelling of an Integer binder names the same binder.
        // A C variable that is no Integer binder stays `Untyped`.
        SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::Named(name),
        )) if typing.is_integer_binding(&name) => SurfaceTerm::Name {
            name,
            ty: LeafType::Integer,
        },
        term => SurfaceTerm::Untyped(term),
    }
}

impl Elaborator<'_> {
    /// The native Surface form of an operand of a native comparison, in the
    /// lowering context it is lowered in: its `-`, `*`, `/`, `%`, shifts and
    /// bitwise operators are native arithmetic, and every other construct
    /// stays `Untyped`. A `-` is a backward pointer step when its left
    /// operand is a pointer with an element width and its right is not, as
    /// lowering decides; a `-` that lowering would refuse as an untyped
    /// pointer step stays `Untyped`, so lowering refuses it as before. A `+`
    /// is elaborated by `native_addition`.
    fn native_surface_term(&self, term: SyntaxTerm, typing: &TypingEnvironment<'_>) -> SurfaceTerm {
        use ArithmeticOperator as Op;
        if matches!(term, SyntaxTerm::Subtract(..))
            && self.refuse_untyped_pointer_access(&term, typing).is_err()
        {
            return SurfaceTerm::Untyped(term);
        }
        if matches!(term, SyntaxTerm::Add(..)) {
            return self.native_addition(term, typing);
        }
        let binary = |op, left, right| SurfaceTerm::Binary {
            op,
            kind: ArithmeticKind::Native,
            left,
            right,
        };
        match term {
            SyntaxTerm::Subtract(left, right) => {
                match (
                    self.contract_pointer_element_width(&left, typing),
                    self.contract_pointer_element_width(&right, typing),
                ) {
                    (Some(element_width), None) => SurfaceTerm::PointerStep {
                        pointer: Box::new(self.native_surface_term(*left, typing)),
                        elements: Box::new(self.native_surface_term(*right, typing)),
                        element_width,
                        backward: true,
                    },
                    _ => binary(
                        Op::Subtract,
                        Box::new(self.native_surface_term(*left, typing)),
                        Box::new(self.native_surface_term(*right, typing)),
                    ),
                }
            }
            SyntaxTerm::Multiply(left, right) => binary(
                Op::Multiply,
                Box::new(self.native_surface_term(*left, typing)),
                Box::new(self.native_surface_term(*right, typing)),
            ),
            SyntaxTerm::Divide(left, right) => binary(
                Op::Divide,
                Box::new(self.native_surface_term(*left, typing)),
                Box::new(self.native_surface_term(*right, typing)),
            ),
            SyntaxTerm::Remainder(left, right) => binary(
                Op::Remainder,
                Box::new(self.native_surface_term(*left, typing)),
                Box::new(self.native_surface_term(*right, typing)),
            ),
            SyntaxTerm::ShiftLeft(left, right) => binary(
                Op::ShiftLeft,
                Box::new(self.native_surface_term(*left, typing)),
                Box::new(self.native_surface_term(*right, typing)),
            ),
            SyntaxTerm::RustShiftLeft(left, right) => binary(
                Op::RustShiftLeft,
                Box::new(self.native_surface_term(*left, typing)),
                Box::new(self.native_surface_term(*right, typing)),
            ),
            SyntaxTerm::ShiftRight(left, right) => binary(
                Op::ShiftRight,
                Box::new(self.native_surface_term(*left, typing)),
                Box::new(self.native_surface_term(*right, typing)),
            ),
            SyntaxTerm::RustShiftRight(left, right) => binary(
                Op::RustShiftRight,
                Box::new(self.native_surface_term(*left, typing)),
                Box::new(self.native_surface_term(*right, typing)),
            ),
            SyntaxTerm::BitwiseAnd(left, right) => binary(
                Op::BitwiseAnd,
                Box::new(self.native_surface_term(*left, typing)),
                Box::new(self.native_surface_term(*right, typing)),
            ),
            SyntaxTerm::BitwiseOr(left, right) => binary(
                Op::BitwiseOr,
                Box::new(self.native_surface_term(*left, typing)),
                Box::new(self.native_surface_term(*right, typing)),
            ),
            SyntaxTerm::BitwiseXor(left, right) => binary(
                Op::BitwiseXor,
                Box::new(self.native_surface_term(*left, typing)),
                Box::new(self.native_surface_term(*right, typing)),
            ),
            SyntaxTerm::BitwiseNot(operand) => SurfaceTerm::BitwiseNot {
                operand: Box::new(self.native_surface_term(*operand, typing)),
            },
            // Lowering refuses the negation of an Integer and reads `-n` of
            // an `int32` literal as that constant; both stay `Untyped`, so
            // lowering does so again.
            SyntaxTerm::Negate(operand)
                if !matches!(operand.as_ref(), SyntaxTerm::IntegerLiteral(value)
                        if value.parse::<u64>().is_ok_and(|value| value <= (i32::MAX as u64) + 1))
                    && !self.contract_expression_is_integer(&operand, typing) =>
            {
                SurfaceTerm::Negate {
                    kind: ArithmeticKind::Native,
                    operand: Box::new(self.native_surface_term(*operand, typing)),
                }
            }
            // A C variable with a known declared type is a typed name; one
            // with no known type stays `Untyped`.
            SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => match self.program_name_type(name.as_str(), typing) {
                Some(ty) => SurfaceTerm::Name {
                    name,
                    ty: LeafType::Program(ty),
                },
                None => SurfaceTerm::Untyped(SyntaxTerm::ProgramExpression(
                    ProgramExpression::Variable(crate::kernel::BindingName::Named(name)),
                )),
            },
            // C types an unsuffixed decimal constant by its value. One too
            // large for `uint64` stays `Untyped`: lowering refuses it.
            SyntaxTerm::IntegerLiteral(text) => match text.parse::<u64>() {
                Ok(value) => SurfaceTerm::IntegerLiteral {
                    text,
                    ty: LeafType::Program(if value <= i32::MAX as u64 {
                        ProgramType::Int32
                    } else if value <= i64::MAX as u64 {
                        ProgramType::Int64
                    } else {
                        ProgramType::UInt64
                    }),
                },
                Err(_) => SurfaceTerm::Untyped(SyntaxTerm::IntegerLiteral(text)),
            },
            term => SurfaceTerm::Untyped(term),
        }
    }

    /// The native Surface form of `left + right`, decided as lowering decides
    /// it, with the same checks in the same order:
    ///
    /// - one lowering refuses as an untyped pointer step, or reads as a chain
    ///   of literal additions to a non-pointer base, stays `Untyped`;
    /// - a call result's pointer element width on either side, then a
    ///   pointer element width on the left, then on the right, makes a
    ///   forward pointer step from that side;
    /// - an operand read through a call's copied parameter stays `Untyped`,
    ///   since lowering decides that step from the lowered read;
    /// - anything else is native `Add`.
    ///
    /// A check that fails leaves the term `Untyped`, so lowering reports the
    /// same error.
    fn native_addition(&self, term: SyntaxTerm, typing: &TypingEnvironment<'_>) -> SurfaceTerm {
        let SyntaxTerm::Add(left, right) = &term else {
            unreachable!("native_addition elaborates an addition");
        };
        if self.refuse_untyped_pointer_access(&term, typing).is_err() {
            return SurfaceTerm::Untyped(term);
        }
        // The literal chain `base + 1 + 2 + ...` lowering reads iteratively.
        let mut literals = 0;
        let mut base = &term;
        while let SyntaxTerm::Add(inner, literal) = base {
            if !matches!(literal.as_ref(), SyntaxTerm::IntegerLiteral(_)) {
                literals = 0;
                break;
            }
            literals += 1;
            base = inner;
        }
        if literals > 0 {
            // As lowering does: the call width is read only for a base with
            // no pointer element type.
            if self.contract_pointer_element_type(base, typing).is_none()
                && !matches!(self.call_pointer_element_width(base, typing), Ok(Some(_)))
            {
                return SurfaceTerm::Untyped(term);
            }
        }
        let step = |pointer: &SyntaxTerm, elements: &SyntaxTerm, element_width| {
            (pointer.clone(), elements.clone(), element_width)
        };
        let chosen = match self.call_pointer_element_width(left, typing) {
            Err(_) => return SurfaceTerm::Untyped(term),
            Ok(Some(width)) => Some(step(left, right, width)),
            Ok(None) => match self.call_pointer_element_width(right, typing) {
                Err(_) => return SurfaceTerm::Untyped(term),
                Ok(Some(width)) => Some(step(right, left, width)),
                Ok(None) => self
                    .contract_pointer_element_width(left, typing)
                    .map(|width| step(left, right, width))
                    .or_else(|| {
                        self.contract_pointer_element_width(right, typing)
                            .map(|width| step(right, left, width))
                    }),
            },
        };
        if let Some((pointer, elements, element_width)) = chosen {
            return SurfaceTerm::PointerStep {
                pointer: Box::new(self.native_surface_term(pointer, typing)),
                elements: Box::new(self.native_surface_term(elements, typing)),
                element_width,
                backward: false,
            };
        }
        let copied_parameter_read = |operand: &SyntaxTerm| {
            let mut operand = operand;
            while let SyntaxTerm::At {
                expression: inner, ..
            }
            | SyntaxTerm::Old(inner)
            | SyntaxTerm::Exact(inner) = operand
            {
                operand = inner;
            }
            region_parameter_read(operand).is_some()
        };
        if copied_parameter_read(left) || copied_parameter_read(right) {
            return SurfaceTerm::Untyped(term);
        }
        let SyntaxTerm::Add(left, right) = term else {
            unreachable!()
        };
        SurfaceTerm::Binary {
            op: ArithmeticOperator::Add,
            kind: ArithmeticKind::Native,
            left: Box::new(self.native_surface_term(*left, typing)),
            right: Box::new(self.native_surface_term(*right, typing)),
        }
    }
}
