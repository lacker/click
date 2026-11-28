//! Elaboration's type queries, apart from the lowerer
//! (`design/typed-surface.md`). An `Elaborator` reads the declarations, the
//! specification definitions, the recorded states and a typing environment,
//! and nothing that lowering builds, so elaboration can be run without
//! lowering. The lowerer builds one for each query and delegates to it.
//! Names at another program point (`old(..)`, `at(..)`) are typed in the
//! scope there, which the outer `TypeScope` builds from the inputs here.
use super::*;

#[derive(Clone)]
pub(super) struct Elaborator<'a> {
    pub(super) declarations: Declarations<'a>,
    pub(super) definitions: SpecDefinitions<'a>,
    pub(super) retained_states: Option<&'a RecordedStates>,
    /// The names a capture reads, which a scope at a recorded state binds.
    pub(super) capture_referenced_names: Option<Arc<BTreeSet<String>>>,
    /// The last generic instantiation that failed to infer its types. The
    /// lowerer reads it to tell a type error from another failure.
    pub(super) type_inference_failure: std::cell::RefCell<Option<String>>,
}

impl<'a> AnnotationLowerer<'a> {
    /// The lowerer's elaboration queries, as a value independent of it.
    pub(super) fn elaborator(&self) -> Elaborator<'a> {
        Elaborator {
            declarations: self.declarations(),
            definitions: self.spec_definitions,
            retained_states: self.retained_states,
            capture_referenced_names: self.capture_referenced_names.clone(),
            type_inference_failure: std::cell::RefCell::new(None),
        }
    }

    /// Run `elaborate` on the lowerer's `Elaborator`, keeping the type
    /// inference failure it records, as lowering recorded its own.
    pub(super) fn with_elaborator<T>(&mut self, elaborate: impl FnOnce(&Elaborator<'_>) -> T) -> T {
        let elaborator = self.elaborator();
        let result = elaborate(&elaborator);
        if let Some(failure) = elaborator.type_inference_failure.take() {
            self.type_inference_failure = Some(failure);
        }
        result
    }
}

impl<'a> Elaborator<'a> {
    /// An `Elaborator` for `function`'s contract, from its declarations
    /// alone, with no lowerer and no kernel state.
    pub(super) fn of_function(
        function: &crate::languages::interface::ImportedFunction,
        definitions: SpecDefinitions<'a>,
    ) -> Self {
        Elaborator {
            declarations: Declarations::of_function(function),
            definitions,
            retained_states: None,
            capture_referenced_names: None,
            type_inference_failure: Default::default(),
        }
    }
}

/// Debug builds: the Surface stored for a clause, with its binder forms
/// read as written, is what elaborating the clause where it is lowered
/// gives, so lowering the stored Surface lowers what lowering the Syntax
/// would (`design/typed-surface.md`).
#[cfg(debug_assertions)]
pub(super) fn check_stored_elaboration(
    lowerer: &AnnotationLowerer<'_>,
    stored: &SurfaceProposition<'_>,
    proposition: &SyntaxProposition,
    context: &SpecElaborationContext,
) {
    crate::instrumentation::uncharged_debug_check(|| {
        assert_eq!(
            stored.with_binder_forms_as_written(),
            lowerer
                .elaborator()
                .elaborate_proposition(proposition, &TypingEnvironment::of(context)),
            "clause `{proposition:?}`: its stored Surface is not what elaborating it here gives"
        );
    });
}

impl Elaborator<'_> {
    fn record_type_inference_failure(&self, message: &str) {
        *self.type_inference_failure.borrow_mut() = Some(message.to_string());
    }

    /// What a scope at another program point is built from.
    fn point_inputs(&self) -> PointInputs<'_> {
        PointInputs {
            entry_values: &self.declarations.entry_values,
            entry_point: self
                .declarations
                .entry_state
                .map(|entry_state| entry_state.program_point()),
            retained_states: self.retained_states,
            capture_referenced_names: self.capture_referenced_names.as_deref(),
        }
    }

    pub(super) fn program_name_type(
        &self,
        name: impl Into<crate::kernel::BindingName>,
        typing: &TypingEnvironment<'_>,
    ) -> Option<ProgramType> {
        self.declarations.program_name_type(name, typing)
    }

    pub(super) fn program_expression_array_element_type(
        &self,
        expression: &ProgramExpression,
        typing: &TypingEnvironment<'_>,
    ) -> Option<ProgramType> {
        self.declarations
            .program_expression_array_element_type(expression, typing)
    }

    pub(super) fn contract_expression_is_integer(
        &self,
        expression: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
    ) -> bool {
        let mut depth = 0;
        let mut current = expression;
        while let SyntaxTerm::Add(left, right) = current {
            if !matches!(right.as_ref(), SyntaxTerm::IntegerLiteral(_)) {
                break;
            }
            depth += 1;
            current = left;
        }
        if depth > 128 && matches!(current, SyntaxTerm::IntegerLiteral(_)) {
            return false;
        }
        self.contract_expression_click_type(expression, typing)
            .is_some_and(|click_type| click_type == ClickType::Integer)
    }

    /// Infer the result kind needed when choosing between the C and Integer
    /// lowering paths.  Surface validation already checks algebraic match
    /// arms against their datatype schema, but the fixed-state lowerer does
    /// not retain that result type in the syntax tree.  Recover it here so a
    /// match whose arms return an Integer binding is still recognized when
    /// the other comparison operand is an untyped numeral.
    pub(super) fn contract_expression_click_type(
        &self,
        expression: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
    ) -> Option<ClickType> {
        self.contract_expression_click_type_in_scope(expression, typing, &mut Vec::new())
    }

    pub(super) fn contract_expression_click_type_in_scope(
        &self,
        expression: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
        lexical_bindings: &mut Vec<(SurfaceBinder, Option<ClickType>)>,
    ) -> Option<ClickType> {
        if let Some(id) = expression.generated_binder() {
            if let Some((_, ty)) = lexical_bindings
                .iter()
                .rev()
                .find(|(name, _)| name == &SurfaceBinder::Generated(id))
            {
                return ty.clone();
            }
            return typing.binding_click_type(&id);
        }

        match expression {
            SyntaxTerm::IntegerContext(_) => Some(ClickType::Integer),
            // A Rust slice's components: its length and its data pointer
            // (`design/rust-slice-values.md`, step 3b).
            SyntaxTerm::ProgramExpression(ProgramExpression::SliceLength(_)) => {
                Some(ClickType::Program(InterfaceType::UInt64(
                    crate::languages::c::syntax::LongRank::Long,
                )))
            }
            SyntaxTerm::ProgramExpression(ProgramExpression::SliceData(slice)) => {
                match self.declarations.slice_expression_type(slice, typing)? {
                    ProgramType::SlicePointer(element) => Some(ClickType::Program(
                        crate::surface::generics::interface_type_from_program_type(
                            element.thin_pointer_type(),
                        ),
                    )),
                    _ => None,
                }
            }

            SyntaxTerm::Lambda {
                parameters, result, ..
            } => Some(lambdas::signature(parameters, result)),
            SyntaxTerm::Apply { function, .. } => match self
                .contract_expression_click_type_in_scope(function, typing, lexical_bindings)?
            {
                ClickType::Function { result, .. } => Some(*result),
                _ => None,
            },

            SyntaxTerm::ResourceField(access) => access.click_type.clone(),
            SyntaxTerm::IntegerLiteral(_) => None,
            SyntaxTerm::Binding(name) => {
                if let Some((_, click_type)) = lexical_bindings
                    .iter()
                    .rev()
                    .find(|(binding, _)| binding == name)
                {
                    click_type.clone()
                } else {
                    typing.binding_click_type(name)
                }
            }
            SyntaxTerm::AlgebraicVariable { algebraic_type, .. }
            | SyntaxTerm::AlgebraicConstructor { algebraic_type, .. } => {
                Some(ClickType::Algebraic(algebraic_type.clone()))
            }
            SyntaxTerm::Negate(inner)
            | SyntaxTerm::Old(inner)
            | SyntaxTerm::Exact(inner)
            | SyntaxTerm::At {
                expression: inner, ..
            } => self.contract_expression_click_type_in_scope(inner, typing, lexical_bindings),
            SyntaxTerm::Add(left, right)
            | SyntaxTerm::Subtract(left, right)
            | SyntaxTerm::Multiply(left, right) => {
                let left =
                    self.contract_expression_click_type_in_scope(left, typing, lexical_bindings);
                let right =
                    self.contract_expression_click_type_in_scope(right, typing, lexical_bindings);
                if left == Some(ClickType::Integer) || right == Some(ClickType::Integer) {
                    Some(ClickType::Integer)
                } else {
                    left.or(right)
                }
            }
            SyntaxTerm::RangeFold {
                start,
                end,
                initial,
                accumulator,
                item,
                body,
                ..
            } => {
                // The index carrier and accumulator carrier are independent.
                // In particular, an Int32 index can feed a C array load while
                // `to_integer(...)` makes the accumulator mathematical.  A
                // fold's result follows the accumulator/body type; the
                // endpoint type only selects the item carrier in the body.
                let start_type =
                    self.contract_expression_click_type_in_scope(start, typing, lexical_bindings);
                let end_type =
                    self.contract_expression_click_type_in_scope(end, typing, lexical_bindings);
                let integer_index =
                    start_type == Some(ClickType::Integer) || end_type == Some(ClickType::Integer);
                let initial_type =
                    self.contract_expression_click_type_in_scope(initial, typing, lexical_bindings);
                let lexical_len = lexical_bindings.len();
                let accumulator_type = initial_type.clone();
                lexical_bindings.push((accumulator.clone(), accumulator_type));
                lexical_bindings.push((
                    item.clone(),
                    if integer_index {
                        Some(ClickType::Integer)
                    } else {
                        Some(ClickType::Program(InterfaceType::Int32))
                    },
                ));
                let body_type =
                    self.contract_expression_click_type_in_scope(body, typing, lexical_bindings);
                lexical_bindings.truncate(lexical_len);
                if initial_type == Some(ClickType::Integer) || body_type == Some(ClickType::Integer)
                {
                    Some(ClickType::Integer)
                } else {
                    initial_type.or(body_type)
                }
            }
            SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => {
                if let Some((_, click_type)) = lexical_bindings
                    .iter()
                    .rev()
                    .find(|(binding, _)| binding == name)
                {
                    click_type.clone()
                } else {
                    typing.binding_click_type(name)
                }
            }
            SyntaxTerm::ProgramBinding(name) => lexical_bindings
                .iter()
                .rev()
                .find_map(|(binding, click_type)| (binding == name).then(|| click_type.clone()))
                .flatten()
                .or_else(|| typing.program_binding_click_type(name)),
            // A slice a Rust call returned is of its slice type
            // (`design/rust-slice-values.md`, step 3c-i), so `slice::len(R)`
            // and `slice::as_ptr(R)` infer their element.
            SyntaxTerm::RegionResult(region) => match self
                .retained_states?
                .region_result_value_at(region, typing.call_result_point())
                .ok()?
            {
                ProgramValue::Pointer(pointer) if pointer.is_wide() => match pointer.program_type()
                {
                    ProgramType::SlicePointer(element) => {
                        Some(ClickType::Program(InterfaceType::Slice(element)))
                    }
                    _ => None,
                },
                _ => None,
            },
            SyntaxTerm::Let {
                name,
                click_type: Some(ClickType::Integer),
                value: _,
                body,
            } => {
                lexical_bindings.push((name.clone(), Some(ClickType::Integer)));
                let body_type =
                    self.contract_expression_click_type_in_scope(body, typing, lexical_bindings);
                lexical_bindings.pop();
                body_type
            }
            SyntaxTerm::Let {
                name,
                click_type: _,
                value,
                body,
            } => {
                let value_type =
                    self.contract_expression_click_type_in_scope(value, typing, lexical_bindings);
                lexical_bindings.push((name.clone(), value_type));
                let body_type =
                    self.contract_expression_click_type_in_scope(body, typing, lexical_bindings);
                lexical_bindings.pop();
                body_type
            }
            SyntaxTerm::AlgebraicMatch { scrutinee, arms } => {
                let Some(ClickType::Algebraic(application)) = self
                    .contract_expression_click_type_in_scope(scrutinee, typing, lexical_bindings)
                else {
                    return None;
                };
                let Ok(algebraic_type) =
                    algebraic_kernel_type(self.definitions.functions, &application)
                else {
                    return None;
                };
                let variants = algebraic_type
                    .variants
                    .iter()
                    .map(|variant| (variant.name.as_str(), variant))
                    .collect::<BTreeMap<_, _>>();
                crate::instrumentation::record_deterministic_work(algebraic_type.variants.len());
                let mut result_type = None;
                let mut has_contextual_literal = false;
                for arm in arms {
                    crate::instrumentation::record_deterministic_work(1);
                    let variant = variants.get(arm.variant.as_str())?;
                    if arm.bindings.len() != variant.fields.len() {
                        return None;
                    }
                    let lexical_len = lexical_bindings.len();
                    for (binding, field) in arm.bindings.iter().zip(&variant.fields) {
                        lexical_bindings.push((
                            binding.clone(),
                            Some(generics::click_type_from_algebraic_value_type(field)),
                        ));
                    }
                    let arm_type = self.contract_expression_click_type_in_scope(
                        &arm.body,
                        typing,
                        lexical_bindings,
                    );
                    lexical_bindings.truncate(lexical_len);
                    let Some(arm_type) = arm_type else {
                        if is_unsuffixed_integer_literal_expression(&arm.body) {
                            // A numeral arm stays untyped until another arm
                            // supplies the match result carrier.  In
                            // particular, do not make an all-literal match
                            // mathematical Integer by default.
                            has_contextual_literal = true;
                            continue;
                        }
                        return None;
                    };
                    if let Some(previous) = &result_type
                        && previous != &arm_type
                    {
                        return None;
                    }
                    result_type = Some(arm_type);
                }
                if has_contextual_literal
                    && !matches!(
                        result_type.as_ref(),
                        Some(ClickType::Integer) | Some(ClickType::Program(_))
                    )
                {
                    return None;
                }
                result_type
            }
            // An Integer conditional: Integer branches, or one Integer branch
            // and an unsuffixed numeral, which takes its type. Any other
            // conditional keeps its C lowering, so it is not typed here.
            SyntaxTerm::If {
                then_branch,
                else_branch,
                ..
            } => {
                let then_type = self.contract_expression_click_type_in_scope(
                    then_branch,
                    typing,
                    lexical_bindings,
                );
                let else_type = self.contract_expression_click_type_in_scope(
                    else_branch,
                    typing,
                    lexical_bindings,
                );
                let integer_or_numeral = |branch_type: &Option<ClickType>, branch| {
                    *branch_type == Some(ClickType::Integer)
                        || (branch_type.is_none()
                            && is_unsuffixed_integer_literal_expression(branch))
                };
                ((then_type == Some(ClickType::Integer) || else_type == Some(ClickType::Integer))
                    && integer_or_numeral(&then_type, then_branch)
                    && integer_or_numeral(&else_type, else_branch))
                .then_some(ClickType::Integer)
            }
            SyntaxTerm::Call { name, .. }
                if name == "to_integer" || is_integer_truncation(name) =>
            {
                Some(ClickType::Integer)
            }
            SyntaxTerm::Call { name, .. } => self
                .definitions
                .functions
                .get(name)
                .map(|function| function.return_type().clone()),
            _ => None,
        }
    }

    /// The Rust enum type of C name `name`, a parameter, local or `result`
    /// that holds an enum's value.
    pub(super) fn enum_program_name_type(
        &self,
        name: &str,
        typing: &TypingEnvironment<'_>,
    ) -> Option<crate::kernel::TypeParameterName> {
        match self.program_name_type(name, typing)? {
            ProgramType::Parameter(enum_type) if crate::surface::holds_spec_value(enum_type) => {
                Some(enum_type)
            }
            _ => None,
        }
    }

    /// The enum or library value type named by a program binding or read.
    pub(super) fn enum_program_value_type(
        &self,
        expression: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
    ) -> Option<crate::kernel::TypeParameterName> {
        match expression {
            SyntaxTerm::Binding(name)
            | SyntaxTerm::ProgramBinding(name)
            | SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => self.enum_program_name_type(name, typing),
            SyntaxTerm::ProgramExpression(ProgramExpression::Load(pointer)) => {
                let value_type = match pointer.as_ref() {
                    ProgramExpression::Variable(name) => {
                        self.program_name_type(name, typing)?.pointee_type()?
                    }
                    _ => self.program_expression_array_element_type(pointer, typing)?,
                };
                match value_type {
                    ProgramType::Parameter(ty) if crate::surface::holds_spec_value(ty) => Some(ty),
                    _ => None,
                }
            }
            SyntaxTerm::MemoryLoad {
                value_type: ProgramType::Parameter(ty),
                ..
            } if crate::surface::holds_spec_value(*ty) => Some(*ty),
            SyntaxTerm::Old(inner) => self.enum_program_value_type(inner, typing),
            // The enum value a call returned.
            SyntaxTerm::RegionResult(region) => {
                match self
                    .retained_states?
                    .region_result_value_at(region, typing.call_result_point())
                    .ok()?
                {
                    ProgramValue::Parameter(term) => {
                        let enum_type = crate::kernel::TypeParameterName::of(&term.algebraic_type);
                        crate::surface::holds_spec_value(enum_type).then_some(enum_type)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    pub(super) fn contract_pointer_element_type(
        &self,
        expression: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
    ) -> Option<ProgramType> {
        match expression {
            SyntaxTerm::MemoryLoad { value_type, .. } => value_type.pointee_type(),
            SyntaxTerm::ResourceField(access) => access
                .click_type
                .as_ref()?
                .interface_type()?
                .pointee_type()
                .map(InterfaceType::to_kernel_type),
            SyntaxTerm::CUnary { operand, lowered } => match lowered {
                ProgramExpression::Cast { target_type, .. } => target_type.pointee_type(),
                ProgramExpression::PointerOffsetBytes { .. } => {
                    self.contract_pointer_element_type(operand, typing)
                }
                _ => self.program_expression_array_element_type(lowered, typing),
            },
            SyntaxTerm::ProgramBinding(name) => typing
                .bound_array_element_type(name)
                .or_else(|| typing.bound_pointer_pointee_type(name)),
            SyntaxTerm::QualifiedC {
                lowered: expression,
                ..
            }
            | SyntaxTerm::ProgramExpression(expression)
            | SyntaxTerm::Field {
                lowered: expression,
                ..
            } => self.program_expression_array_element_type(expression, typing),
            SyntaxTerm::Old(expression)
            | SyntaxTerm::Exact(expression)
            | SyntaxTerm::At { expression, .. } => {
                self.contract_pointer_element_type(expression, typing)
            }
            SyntaxTerm::Add(left, right) => self
                .contract_pointer_element_type(left, typing)
                .or_else(|| self.contract_pointer_element_type(right, typing)),
            SyntaxTerm::Subtract(left, _) => self.contract_pointer_element_type(left, typing),
            _ => None,
        }
    }

    /// The element type a contract expression steps by when it is a pointer:
    /// an array reference or a pointer-valued binding in scope, a pointer
    /// fragment, or pointer arithmetic on one. `None` for a scalar.
    /// Whether a contract cast's operand is a `void *`, by its Surface type or,
    /// for a C name, by its declared type.
    pub(super) fn contract_operand_is_void_pointer(
        &self,
        operand: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
    ) -> bool {
        if matches!(
            self.contract_expression_click_type(operand, typing),
            Some(ClickType::Program(InterfaceType::VoidPointer))
        ) {
            return true;
        }
        match operand {
            SyntaxTerm::ProgramExpression(ProgramExpression::Variable(name)) => {
                self.declarations.c_variable_type(name.clone()) == Some(ProgramType::VoidPointer)
            }
            // A name bound to a `void *` value, whatever object it may name.
            SyntaxTerm::ProgramBinding(name) => {
                typing
                    .program_binding_click_type(name)
                    .and_then(|click_type| click_type.interface_type())
                    == Some(InterfaceType::VoidPointer)
            }
            SyntaxTerm::Old(expression)
            | SyntaxTerm::Exact(expression)
            | SyntaxTerm::At { expression, .. } => {
                self.contract_operand_is_void_pointer(expression, typing)
            }
            _ => false,
        }
    }
    /// The spelling of `operand`'s type when it is a pointer that states no
    /// pointee type ([`pointee_less_pointer_spelling`]): a cast to one, a
    /// `load` of one, a byte offset of one, or a binding, parameter or call
    /// of that type.
    pub(super) fn pointee_less_operand(
        &self,
        operand: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
    ) -> Option<&'static str> {
        let spelling = match operand {
            SyntaxTerm::CUnary { operand, lowered } => self
                .pointee_less_program_operand(lowered, typing)
                .or_else(|| {
                    matches!(lowered, ProgramExpression::PointerOffsetBytes { .. })
                        .then(|| self.pointee_less_operand(operand, typing))
                        .flatten()
                }),
            SyntaxTerm::ProgramExpression(lowered) => {
                self.pointee_less_program_operand(lowered, typing)
            }
            SyntaxTerm::Old(inner)
            | SyntaxTerm::Exact(inner)
            | SyntaxTerm::At {
                expression: inner, ..
            } => self.pointee_less_operand(inner, typing),
            // A call's recorded `void *` result.
            SyntaxTerm::RegionResult(region) => {
                match self.retained_states.and_then(|states| {
                    states
                        .region_result_value_at(region, typing.call_result_point())
                        .ok()
                }) {
                    Some(ProgramValue::Pointer(pointer)) => {
                        pointee_less_pointer_spelling(pointer.program_type())
                    }
                    _ => None,
                }
            }
            _ => match self.contract_expression_click_type(operand, typing) {
                Some(ClickType::Program(operand_type)) => {
                    pointee_less_pointer_spelling(operand_type.to_kernel_type())
                }
                _ => None,
            },
        };
        spelling.or_else(|| {
            self.contract_operand_is_void_pointer(operand, typing)
                .then_some("void *")
        })
    }
    /// [`Self::pointee_less_operand`] for a lowered C fragment.
    pub(super) fn pointee_less_program_operand(
        &self,
        operand: &ProgramExpression,
        typing: &TypingEnvironment<'_>,
    ) -> Option<&'static str> {
        match operand {
            ProgramExpression::Cast { target_type, .. } => {
                pointee_less_pointer_spelling(*target_type)
            }
            ProgramExpression::TypedLoad { value_type, .. } => {
                pointee_less_pointer_spelling(*value_type)
            }
            ProgramExpression::Value(ProgramValue::Pointer(pointer)) => {
                pointee_less_pointer_spelling(pointer.program_type())
            }
            ProgramExpression::PointerOffsetBytes { pointer, .. } => {
                self.pointee_less_program_operand(pointer, typing)
            }
            ProgramExpression::Add(left, right) | ProgramExpression::Subtract(left, right) => self
                .pointee_less_program_operand(left, typing)
                .or_else(|| self.pointee_less_program_operand(right, typing)),
            ProgramExpression::Variable(name @ crate::kernel::BindingName::Named(_)) => match self
                .contract_expression_click_type(
                    &SyntaxTerm::ProgramExpression(operand.clone()),
                    typing,
                ) {
                Some(ClickType::Program(operand_type)) => {
                    pointee_less_pointer_spelling(operand_type.to_kernel_type())
                }
                _ => None,
            }
            .or_else(|| {
                self.declarations
                    .c_variable_type(name.clone())
                    .and_then(pointee_less_pointer_spelling)
            }),
            _ => None,
        }
    }
    /// Refuses `*q` and `q[i]` when `q` is a `Pointer` or a `void *`, and
    /// `q + k` and `q - k` when `q` is a `Pointer`: it has no pointee type to
    /// read at or step by. A `void *` steps by one byte, as in C.
    pub(super) fn refuse_untyped_pointer_access(
        &self,
        expression: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
    ) -> Result<(), String> {
        let refused_program = |lowered: &ProgramExpression| match lowered {
            ProgramExpression::Load(pointer) | ProgramExpression::Index(pointer, _) => {
                self.pointee_less_program_operand(pointer, typing)
            }
            ProgramExpression::Add(left, right) | ProgramExpression::Subtract(left, right) => {
                pointee_less_step_refusal(
                    self.pointee_less_program_operand(left, typing),
                    self.pointee_less_program_operand(right, typing),
                    matches!(lowered, ProgramExpression::Subtract(..)),
                )
            }
            _ => None,
        };
        let refused = match expression {
            SyntaxTerm::CUnary { operand, lowered } => refused_program(lowered).or_else(|| {
                matches!(
                    lowered,
                    ProgramExpression::Load(_) | ProgramExpression::Index(..)
                )
                .then(|| self.pointee_less_operand(operand, typing))
                .flatten()
            }),
            SyntaxTerm::ProgramExpression(lowered) => refused_program(lowered),
            SyntaxTerm::ArrayIndex { base, lowered, .. } => {
                refused_program(lowered).or_else(|| self.pointee_less_operand(base, typing))
            }
            SyntaxTerm::Index(base, _) => self.pointee_less_operand(base, typing),
            SyntaxTerm::Add(left, right) | SyntaxTerm::Subtract(left, right) => {
                pointee_less_step_refusal(
                    self.pointee_less_operand(left, typing),
                    self.pointee_less_operand(right, typing),
                    matches!(expression, SyntaxTerm::Subtract(..)),
                )
            }
            _ => None,
        };
        match refused {
            Some(spelling) => Err(pointee_less_access_message(spelling)),
            None => Ok(()),
        }
    }

    /// Physical element widths take precedence over scalar resource carriers.
    pub(super) fn contract_pointer_element_width(
        &self,
        expression: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
    ) -> Option<u32> {
        match expression {
            SyntaxTerm::RegionResult(region) => {
                let ProgramValue::Pointer(pointer) = self
                    .retained_states?
                    .region_result_value_at(region, typing.call_result_point())
                    .ok()?
                else {
                    return None;
                };
                self.definitions.pointer_element_width(&pointer).ok()
            }
            SyntaxTerm::ProgramBinding(name) => self.program_expression_array_element_width(
                &ProgramExpression::Variable((name.clone()).into()),
                typing,
            ),
            SyntaxTerm::CUnary { lowered, .. }
            | SyntaxTerm::QualifiedC { lowered, .. }
            | SyntaxTerm::ProgramExpression(lowered)
            | SyntaxTerm::Field { lowered, .. } => {
                self.program_expression_array_element_width(lowered, typing)
            }
            SyntaxTerm::Old(inner) | SyntaxTerm::Exact(inner) => {
                self.contract_pointer_element_width(inner, typing)
            }
            SyntaxTerm::At {
                selector,
                expression,
            } => self.contract_pointer_element_width(expression, &typing.at_call(selector)),
            SyntaxTerm::Add(left, right) => self
                .contract_pointer_element_width(left, typing)
                .or_else(|| self.contract_pointer_element_width(right, typing)),
            SyntaxTerm::Subtract(left, _) => self.contract_pointer_element_width(left, typing),
            _ => self
                .contract_pointer_element_type(expression, typing)
                .map(ProgramType::byte_width),
        }
    }

    /// The physical width used by C pointer arithmetic.  A pointer to a
    /// struct has the nominal compatible `int32*` kernel carrier, so its
    /// pointee layout must be consulted before falling back to `ProgramType`.
    pub(super) fn program_expression_array_element_width(
        &self,
        expression: &ProgramExpression,
        typing: &TypingEnvironment<'_>,
    ) -> Option<u32> {
        if let ProgramExpression::Variable(name) = expression
            && let Some(width) =
                name.metadata_in(self.declarations.parameter_pointer_element_widths.as_ref())
        {
            return Some(*width);
        }
        if let Some(element) = self.direct_pointer_element(expression, typing) {
            return self.definitions.element_width(&element).ok();
        }
        if matches!(expression, ProgramExpression::Variable(name) if name.is_named("result"))
            && typing.contract_result_in_scope()
        {
            return self.program_expression_array_element_width(
                &ProgramExpression::Variable(crate::kernel::CONTRACT_RESULT),
                typing,
            );
        }
        match expression {
            ProgramExpression::AddressOf(target)
            | ProgramExpression::CheckedObjectAddress(target)
                if matches!(target.as_ref(), ProgramExpression::Index(..)) =>
            {
                let ProgramExpression::Index(base, _) = target.as_ref() else {
                    unreachable!()
                };
                self.program_expression_array_element_width(base, typing)
            }
            ProgramExpression::AddressOf(target)
            | ProgramExpression::CheckedObjectAddress(target) => match target.as_ref() {
                ProgramExpression::TypedLoad { value_type, .. } => Some(value_type.byte_width()),
                ProgramExpression::Variable(name) => self
                    .declarations
                    .c_variable_type(name)
                    .map(ProgramType::byte_width),
                _ => None,
            },
            ProgramExpression::Value(ProgramValue::Pointer(pointer)) => pointer
                .program_type()
                .pointee_type()
                .map(ProgramType::byte_width),
            ProgramExpression::Cast { target_type, .. } => {
                target_type.pointee_type().map(ProgramType::byte_width)
            }
            // A slice's data pointer steps by its element.
            ProgramExpression::SliceData(_) => self
                .declarations
                .program_expression_array_element_type(expression, typing)
                .map(ProgramType::byte_width),
            ProgramExpression::Variable(name) => name
                .metadata_in(self.declarations.parameter_pointer_element_widths.as_ref())
                .copied()
                .or_else(|| {
                    name.named()
                        .and_then(|name| typing.bound_array_element_type(name))
                        .map(ProgramType::byte_width)
                })
                .or_else(|| {
                    self.declarations
                        .declared_pointer_element_type(name)
                        .map(|ty| ty.byte_width())
                })
                .or_else(|| {
                    (name == &crate::kernel::CONTRACT_RESULT)
                        .then(|| self.declarations.result_type.pointee_type())
                        .flatten()
                        .map(ProgramType::byte_width)
                })
                .or_else(|| {
                    self.declarations
                        .global_array_element_type(name)
                        .map(ProgramType::byte_width)
                }),
            ProgramExpression::TypedLoad { value_type, .. } => match value_type {
                ProgramType::Int32Array(_) => Some(4),
                ProgramType::Int64Array(_) | ProgramType::UInt64Array(_) => Some(8),
                ProgramType::Int128Array(_) | ProgramType::UInt128Array(_) => Some(16),
                ProgramType::UInt8Array(_) => Some(1),
                value_type => value_type.pointee_type().map(ProgramType::byte_width),
            },
            ProgramExpression::PointerOffsetBytes { pointer, .. }
            | ProgramExpression::Subobject { pointer, .. } => {
                self.program_expression_array_element_width(pointer, typing)
            }
            ProgramExpression::Add(left, right) => self
                .program_expression_array_element_width(left, typing)
                .or_else(|| self.program_expression_array_element_width(right, typing)),
            ProgramExpression::Subtract(left, _) => {
                self.program_expression_array_element_width(left, typing)
            }
            _ => None,
        }
    }

    /// The pointer `expression` directly is, by what it steps by: a pointer
    /// value, or a C name bound to one. A name bound to a pointer value never
    /// reaches the declared-type lookups after it, so the lookup that read
    /// such a value's pointee there was never reached and is not kept.
    fn direct_pointer_element(
        &self,
        expression: &ProgramExpression,
        typing: &TypingEnvironment<'_>,
    ) -> Option<crate::surface::PointerElement> {
        match expression {
            ProgramExpression::Value(ProgramValue::Pointer(pointer)) => {
                Some(crate::surface::PointerElement::of(pointer))
            }
            ProgramExpression::Variable(name) => typing.bound_pointer_element(name),
            _ => None,
        }
    }

    /// Whether `expression` calls a generic function whose result type, a
    /// type parameter, is algebraic at this call: `vec::get(v, i)` with `v`
    /// a `Vec<T>` of a theorem's rigid `T`.
    pub(super) fn generic_call_returns_algebraic(
        &self,
        expression: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
    ) -> bool {
        let SyntaxTerm::Call { name, arguments } = expression else {
            return false;
        };
        let Some(definition) = self.definitions.functions.get(name).cloned() else {
            return false;
        };
        if !matches!(definition.return_type(), ClickType::Parameter(_)) {
            return false;
        }
        self.instantiate_click_function_for_call(&definition, arguments, typing)
            .is_ok_and(|instance| matches!(instance.return_type(), ClickType::Algebraic(_)))
    }

    pub(super) fn instantiate_click_function_for_call(
        &self,
        definition: &ClickFunctionDefinition,
        arguments: &[SyntaxTerm],
        typing: &TypingEnvironment<'_>,
    ) -> Result<ClickFunctionDefinition, String> {
        if definition.type_parameters().is_empty() {
            return Ok(definition.clone());
        }
        let argument_types = definition
            .parameters()
            .iter()
            .zip(arguments)
            .map(|(parameter, argument)| {
                self.infer_call_argument_type(parameter.click_type(), argument, typing)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let substitution = generics::infer_type_substitution(
            "function",
            definition.name(),
            definition.type_parameters(),
            definition
                .parameters()
                .iter()
                .map(|parameter| parameter.click_type().clone()),
            argument_types,
        )
        .inspect_err(|message| self.record_type_inference_failure(message))?;
        generics::instantiate_function(definition, &substitution)
    }

    pub(super) fn infer_call_argument_type(
        &self,
        expected: &ClickType,
        argument: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
    ) -> Result<Option<ClickType>, String> {
        match expected {
            ClickType::Resource => Ok(Some(ClickType::Resource)),
            ClickType::Function { .. } => self
                .contract_expression_click_type_in_scope(argument, typing, &mut Vec::new())
                .map(Some)
                .ok_or_else(|| "callback argument needs a concrete lambda".into()),
            ClickType::Proposition => Err("proposition parameters are not supported yet".into()),
            // The argument's type by the rules lowering it would apply, without
            // lowering it.
            ClickType::Algebraic(_) => self.algebraic_argument_click_type(argument, typing),
            // A `T*` parameter binds `T` from the argument's pointer type,
            // as a `T` parameter binds it from the argument's type.
            ClickType::Program(
                InterfaceType::ParameterPointer(_)
                | InterfaceType::Slice(crate::kernel::SliceElement::Parameter(_)),
            )
            | ClickType::Parameter(_) => {
                self.infer_unconstrained_call_argument_type(argument, typing)
            }
            ClickType::Program(_) | ClickType::CObjectPointer { .. } => Ok(Some(expected.clone())),
            ClickType::Integer => Ok(Some(ClickType::Integer)),
        }
    }

    /// The type of an argument passed where an algebraic value is expected,
    /// by the rules lowering such an argument applies, without lowering it:
    /// a program value of an enum or library type is that type's algebraic
    /// value; `old(..)` and `at(..)` type their operand in the scope of the
    /// point they name; a bare name is an algebraic binding or an error; a
    /// call is its instance's result; anything else has its synthesized type.
    /// Over the gate this answered exactly as lowering the argument did,
    /// errors included.
    pub(super) fn algebraic_argument_click_type(
        &self,
        argument: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
    ) -> Result<Option<ClickType>, String> {
        if let Some(enum_type) = self.enum_program_value_type(argument, typing) {
            return Ok(Some(generics::click_type_from_algebraic_value_type(
                &enum_type.algebraic_type().value_type(),
            )));
        }
        match argument {
            // The operand is typed where it is read: a local named in it is
            // one in scope at that point, as lowering reads it there.
            SyntaxTerm::Old(inner) => {
                let entry = typing.at_entry(&self.point_inputs())?;
                self.algebraic_argument_click_type(inner, &TypingEnvironment::in_scope(&*entry))
            }
            SyntaxTerm::At {
                selector,
                expression,
            } => {
                let retained_state =
                    typing.at_point(selector, &self.point_inputs())?.ok_or_else(|| {
                        "algebraic values at unresolved program points are not supported in this slice"
                            .to_string()
                    })?;
                self.algebraic_argument_click_type(
                    expression,
                    &TypingEnvironment::in_scope(&*retained_state),
                )
            }
            // A bare name is an algebraic binding or nothing: an Integer or
            // program binding of that name does not make it algebraic.
            SyntaxTerm::Binding(name)
            | SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => typing
                .algebraic_binding_click_type(name)
                .map(Some)
                .ok_or_else(|| format!("`{name}` is not an algebraic binding in this scope")),
            SyntaxTerm::Call { name, arguments } if name != "to_nat" => {
                let Some(definition) = self.definitions.functions.get(name).cloned() else {
                    return Ok(None);
                };
                let definition =
                    self.instantiate_click_function_for_call(&definition, arguments, typing)?;
                Ok(Some(definition.return_type().clone()))
            }
            _ => {
                Ok(self.contract_expression_click_type_in_scope(argument, typing, &mut Vec::new()))
            }
        }
    }

    pub(super) fn infer_unconstrained_call_argument_type(
        &self,
        argument: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
    ) -> Result<Option<ClickType>, String> {
        if let Some(cast_type) = generics::explicit_cast_click_type(argument) {
            return Ok(Some(cast_type));
        }
        match argument {
            SyntaxTerm::IntegerLiteral(_) | SyntaxTerm::Negate(_) => {
                Ok(generics::default_numeral_click_type(argument))
            }
            SyntaxTerm::Old(inner)
            | SyntaxTerm::Exact(inner)
            | SyntaxTerm::At {
                expression: inner, ..
            } => self.infer_unconstrained_call_argument_type(inner, typing),
            SyntaxTerm::ResourceField(access) => Ok(access.click_type.clone()),
            SyntaxTerm::AlgebraicVariable { algebraic_type, .. }
            | SyntaxTerm::AlgebraicConstructor { algebraic_type, .. } => {
                Ok(Some(ClickType::Algebraic(algebraic_type.clone())))
            }
            // A binder whose value states no type, such as a match arm's
            // slice binder, has the type its binding gives it.
            SyntaxTerm::Binding(name) => Ok(typing
                .algebraic_binding_click_type(name)
                .or_else(|| typing.program_binding_click_type(name))
                .or_else(|| self.contract_expression_click_type(argument, typing))),
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(value)) => {
                Ok(Some(generics::click_type_from_program_value(value)))
            }
            // A Rust slice named as the program resolves it, `program::s`,
            // has its declared slice type.
            SyntaxTerm::ProgramBinding(name)
                if let Some(slice) = self
                    .declarations
                    .local_type_state
                    .and_then(|state| {
                        let id = state.locals().visible_local_declaration(name)?;
                        state.local_object_type(crate::kernel::BindingName::Local(id.clone()))
                    })
                    .filter(|ty| ty.is_slice_pointer())
                    .or_else(|| {
                        self.declarations.slice_expression_type(
                            &ProgramExpression::Variable(name.as_str().into()),
                            typing,
                        )
                    }) =>
            {
                Ok(Some(ClickType::Program(
                    crate::surface::generics::interface_type_from_program_type(slice),
                )))
            }
            // A Rust slice's components, `s.len()` and `s.as_ptr()`, and a
            // slice a Rust call returned (step 3c-i).
            SyntaxTerm::ProgramExpression(
                ProgramExpression::SliceLength(_) | ProgramExpression::SliceData(_),
            )
            | SyntaxTerm::RegionResult(_) => {
                Ok(self.contract_expression_click_type(argument, typing))
            }
            // A program variable, such as a slice parameter passed to a pure
            // function, has its declared type.
            SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => Ok(typing
                .algebraic_binding_click_type(name)
                .or_else(|| typing.program_binding_click_type(name))
                .or_else(|| self.contract_expression_click_type(argument, typing))
                .or_else(|| {
                    // A Rust slice parameter's type is its declared slice
                    // type (`design/rust-slice-values.md`, step 3b).
                    let slice @ ProgramType::SlicePointer(_) =
                        self.declarations.c_variable_type(name.as_str())?
                    else {
                        return None;
                    };
                    Some(ClickType::Program(
                        crate::surface::generics::interface_type_from_program_type(slice),
                    ))
                })),
            SyntaxTerm::Call { name, arguments } => {
                let definition = self
                    .definitions
                    .functions
                    .get(name)
                    .ok_or_else(|| format!("unknown function `{name}`"))?
                    .clone();
                let definition =
                    self.instantiate_click_function_for_call(&definition, arguments, typing)?;
                Ok(Some(definition.return_type().clone()))
            }
            // Pointer arithmetic keeps its pointer's type: `bytes + k` is a
            // `*const u8` as `bytes` is.
            SyntaxTerm::Add(left, right) | SyntaxTerm::Subtract(left, right) => {
                let left = self.infer_unconstrained_call_argument_type(left, typing)?;
                if left
                    .as_ref()
                    .is_some_and(|ty| ty.interface_type().is_some_and(|c| c.is_pointer()))
                {
                    return Ok(left);
                }
                if matches!(argument, SyntaxTerm::Add(..)) {
                    let right = self.infer_unconstrained_call_argument_type(right, typing)?;
                    if right
                        .as_ref()
                        .is_some_and(|ty| ty.interface_type().is_some_and(|c| c.is_pointer()))
                    {
                        return Ok(right);
                    }
                }
                Ok(None)
            }
            // An element's address, `&bytes[1]`, is a pointer to the element.
            SyntaxTerm::ProgramExpression(
                ProgramExpression::AddressOf(_) | ProgramExpression::CheckedObjectAddress(_),
            )
            | SyntaxTerm::CUnary {
                lowered:
                    ProgramExpression::AddressOf(_) | ProgramExpression::CheckedObjectAddress(_),
                ..
            } => Ok(self
                .contract_expression_click_type(argument, typing)
                .or_else(|| self.element_pointer_click_type(argument, typing))),
            _ => Ok(None),
        }
    }

    /// The pointer to the scalar element `pointer` declares, as a Click type.
    fn element_pointer_click_type(
        &self,
        pointer: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
    ) -> Option<ClickType> {
        self.contract_pointer_element_type(pointer, typing)
            .filter(|element| !element.is_pointer())
            .and_then(|element| generics::interface_type_from_program_type(element).pointer_type())
            .map(ClickType::Program)
    }

    /// The element width a pure call's result steps by when the call
    /// returns a pointer: its declared result's pointee, at the call's own
    /// type arguments. `None` for any other expression or result.
    pub(super) fn call_pointer_element_width(
        &self,
        expression: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
    ) -> Result<Option<u32>, String> {
        // A state changes the value read, not the call's declared type.
        if let SyntaxTerm::Old(inner)
        | SyntaxTerm::Exact(inner)
        | SyntaxTerm::At {
            expression: inner, ..
        } = expression
        {
            return self.call_pointer_element_width(inner, typing);
        }
        // Only a declared pure function with a pointer result: a built-in
        // conversion such as `to_int32` is not one.
        let SyntaxTerm::Call { name, .. } = expression else {
            return Ok(None);
        };
        if !self
            .definitions
            .functions
            .get(name)
            .is_some_and(|definition| match definition.return_type() {
                ClickType::Program(interface_type) => {
                    interface_type.is_pointer()
                        || matches!(interface_type, InterfaceType::ParameterPointer(_))
                }
                ClickType::CObjectPointer { .. } => true,
                _ => false,
            })
        {
            return Ok(None);
        }
        Ok(self
            .infer_unconstrained_call_argument_type(expression, typing)?
            .and_then(|result| result.interface_type())
            .and_then(|result| result.pointee_type())
            .map(|element| element.to_kernel_type().byte_width()))
    }

    /// Whether a range's endpoints make its item a `uint64`: one endpoint
    /// is a `uint64`, as for a range fold.
    pub(super) fn range_bounds_are_uint64(
        &self,
        start: &SyntaxTerm,
        end: &SyntaxTerm,
        typing: &TypingEnvironment<'_>,
    ) -> bool {
        [start, end].into_iter().any(|bound| {
            matches!(
                self.contract_expression_click_type(bound, typing),
                Some(ClickType::Program(InterfaceType::UInt64(_)))
            ) || matches!(bound, SyntaxTerm::ProgramExpression(ProgramExpression::Variable(name))
                    if self.declarations.c_variable_type(name) == Some(ProgramType::UInt64))
                || matches!(bound, SyntaxTerm::ProgramExpression(ProgramExpression::Value(value))
                    if value.program_type() == ProgramType::UInt64)
                // A written cast, `n as uint64`, has the type it names.
                || matches!(
                    generics::explicit_cast_click_type(bound),
                    Some(ClickType::Program(InterfaceType::UInt64(_)))
                )
        })
    }

    /// Elaborate a whole clause: its connectives and comparisons, as
    /// `elaborate_proposition` does, and each binder's body in an
    /// environment where the binder has its declared type, or a range item
    /// the type its endpoints give it. A comparison whose elaboration fails
    /// stays `Untyped`, as `elaborate_proposition` leaves it.
    pub(super) fn elaborate_clause<'s>(
        &self,
        proposition: &'s SyntaxProposition,
        typing: &TypingEnvironment<'_>,
    ) -> SurfaceProposition<'s> {
        let mut surface = self.elaborate_proposition(proposition, typing);
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
                SurfaceProposition::Untyped(syntax) => {
                    if let Some(binder) = self.elaborate_binder(syntax, typing) {
                        *node = binder;
                    }
                }
                _ => {}
            }
        }
        surface
    }

    /// The Surface form of a binder form, with its body elaborated by
    /// `elaborate_clause` where the binder is in scope; `None` for any
    /// other construct.
    fn elaborate_binder<'s>(
        &self,
        syntax: &'s SyntaxProposition,
        typing: &TypingEnvironment<'_>,
    ) -> Option<SurfaceProposition<'s>> {
        use crate::surface::typed_surface::Quantifier;
        let quantified = |quantifier, name: &SurfaceBinder, click_type: &ClickType, body| {
            SurfaceProposition::Quantified {
                quantifier,
                name: name.clone(),
                click_type: click_type.clone(),
                body: Box::new(
                    self.elaborate_clause(body, &typing.with_declared(name, click_type.clone())),
                ),
                syntax,
            }
        };
        let range = |quantifier, start, end, item: &SurfaceBinder, body| {
            let item_type = if self.range_bounds_are_uint64(start, end, typing) {
                ProgramType::UInt64
            } else {
                ProgramType::Int32
            };
            SurfaceProposition::Range {
                quantifier,
                item: item.clone(),
                item_type,
                body: Box::new(self.elaborate_clause(
                    body,
                    &typing.with_declared(item, range_item_click_type(item_type)),
                )),
                syntax,
            }
        };
        Some(match syntax {
            SyntaxProposition::ForAll {
                click_type,
                name,
                body,
                ..
            } => quantified(Quantifier::All, name, click_type, body),
            SyntaxProposition::Exists {
                click_type,
                name,
                body,
                ..
            } => quantified(Quantifier::Some, name, click_type, body),
            SyntaxProposition::RangeAll {
                start,
                end,
                item,
                body,
                ..
            } => range(Quantifier::All, start, end, item, body),
            SyntaxProposition::RangeAny {
                start,
                end,
                item,
                body,
                ..
            } => range(Quantifier::Some, start, end, item, body),
            _ => return None,
        })
    }

    /// A function contract clause's Surface, elaborated once before it is
    /// lowered, and the type-inference failure the elaboration recorded.
    pub(super) fn elaborate_contract_clause<'s>(
        &self,
        proposition: &'s SyntaxProposition,
        context: &SpecElaborationContext,
    ) -> (SurfaceProposition<'s>, Option<String>) {
        let surface = self.elaborate_clause(proposition, &TypingEnvironment::of(context));
        (surface, self.type_inference_failure.take())
    }
}

/// A proof clause the proof driver elaborated from the front end's
/// declarations at its position, with the type-inference failure the
/// elaboration recorded, if any. Lowering lowers this Surface instead of
/// elaborating the clause itself (`design/typed-surface.md`).
pub(in crate::surface) struct ElaboratedProofClause<'s> {
    pub(super) surface: SurfaceProposition<'s>,
    pub(super) failure: Option<String>,
}

/// Elaborate a proof clause at its position in `function`: the C names in
/// scope there are `scope`, and the proof binds the Click names in
/// `integer_values` and `algebraic_values`. `None` for a function whose
/// front end records no declarations for them, whose clauses lowering still
/// elaborates itself.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn elaborate_proof_clause<'s>(
    proposition: &'s SyntaxProposition,
    function: &crate::languages::interface::ImportedFunction,
    scope: Option<&syntax::CSourceBindings>,
    integer_values: &PersistentBinderMap<crate::kernel::SpecIntegerExpression>,
    algebraic_values: &BTreeMap<String, SpecAlgebraicExpression>,
    result_in_scope: bool,
    retained_states: &RecordedStates,
    definitions: SpecDefinitions<'_>,
) -> Option<ElaboratedProofClause<'s>> {
    // A front end records the declarations a clause's names resolve to:
    // C's scopes at each position, or the types of the locals Rust's and
    // C++'s bind by spelling.
    if function.body_end_scope().is_none() && function.spelled_local_types().is_none() {
        return None;
    }
    let mut declarations = Declarations::of_function(function);
    declarations.source_bindings = scope.cloned();
    let algebraic_values = algebraic_values.clone().into_iter().collect();
    let declared = super::declared_scope::DeclaredScope {
        declarations: &declarations,
        integer_values,
        algebraic_values: &algebraic_values,
        contract_result_in_scope: result_in_scope,
    };
    let mut captures = BTreeSet::<QuantifierCapture>::new();
    collect_click_proposition_referenced_bindings(proposition, &mut captures);
    let referenced = captures
        .into_iter()
        .filter_map(|capture| match capture {
            QuantifierCapture::Name(name) => Some(name),
            QuantifierCapture::Variable(_) => None,
        })
        .collect();
    let elaborator = Elaborator {
        declarations: declarations.clone(),
        definitions,
        retained_states: Some(retained_states),
        capture_referenced_names: Some(Arc::new(referenced)),
        type_inference_failure: std::cell::RefCell::new(None),
    };
    let surface = elaborator.elaborate_clause(proposition, &TypingEnvironment::in_scope(&declared));
    Some(ElaboratedProofClause {
        surface,
        failure: elaborator.type_inference_failure.take(),
    })
}

impl AnnotationLowerer<'_> {
    /// Lower a proof clause the proof driver elaborated. The failure is held
    /// where in-place elaboration would have left it, as lowering starts.
    pub(super) fn lower_elaborated_proof_clause(
        &mut self,
        clause: &ElaboratedProofClause<'_>,
        proposition: &SyntaxProposition,
        environment: &SpecElaborationContext,
    ) -> Result<SpecProposition, String> {
        // Debug builds, until lowering stops elaborating proof clauses: the
        // driver's elaboration is the one lowering would have made.
        #[cfg(debug_assertions)]
        crate::instrumentation::uncharged_debug_check(|| {
            let elaborator = self.elaborator();
            assert_eq!(
                (
                    &elaborator.elaborate_clause(proposition, &TypingEnvironment::of(environment)),
                    &elaborator.type_inference_failure.take()
                ),
                (&clause.surface, &clause.failure),
                "proof clause `{proposition:?}` elaborates differently from the front end's declarations at its position"
            );
        });
        #[cfg(not(debug_assertions))]
        let _ = proposition;
        if let Some(failure) = &clause.failure {
            self.type_inference_failure = Some(failure.clone());
        }
        self.lower_surface_proposition(&clause.surface, environment)
    }
}

/// The type a range item of `item_type` has, as lowering binds it: the
/// click type of a value of that type.
pub(super) fn range_item_click_type(item_type: ProgramType) -> ClickType {
    ClickType::Program(crate::surface::generics::interface_type_from_program_type(
        item_type,
    ))
}

/// Debug builds: a binder's body elaborates, with the binder declared at
/// `declared`, to the Surface lowering's body context gives it, so a clause
/// can be elaborated with its binders declared before lowering binds them
/// (`design/typed-surface.md`). `outer` is the context the binder form is
/// lowered in.
#[cfg(debug_assertions)]
pub(super) fn check_binder_body_elaboration(
    lowerer: &AnnotationLowerer<'_>,
    outer: &SpecElaborationContext,
    name: &SurfaceBinder,
    declared: &ClickType,
    body: &SyntaxProposition,
    body_environment: &SpecElaborationContext,
) {
    crate::instrumentation::uncharged_debug_check(|| {
        let elaborator = lowerer.elaborator();
        assert_eq!(
            elaborator.elaborate_proposition(
                body,
                &TypingEnvironment::of(outer).with_declared(name, declared.clone()),
            ),
            elaborator.elaborate_proposition(body, &TypingEnvironment::of(body_environment)),
            "binder `{name:?}` declared `{declared:?}`: its body elaborates differently from its lowered context"
        );
    });
}
