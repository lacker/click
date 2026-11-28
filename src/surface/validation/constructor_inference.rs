//! Constructor type-argument inference.
//!
//! `List::Nil` and `List::Cons(x, xs)` leave out the type arguments of a
//! generic datatype. This pass fills them in during declaration expansion,
//! before validation, so every later pass and the kernel see the fully
//! applied `List<T>::Nil` a proof could have written. The arguments come
//! from one of two places: the constructor's own arguments (`Cons(node,
//! rb_inorder(t))` takes `T` from `rb_inorder`'s result), or the type its
//! position expects (a function's result, a call's parameter, the field of
//! an enclosing constructor, the other side of a comparison, or a typed
//! `let`). A constructor neither fixes is left as written, and validation
//! refuses it with the type arguments to write.
//!
//! The work is local: a constructor reads its direct arguments, and an
//! expected type is pushed only into the positions that are still
//! unapplied. Nothing here decides what a program means; an inferred type
//! is checked by validation and lowering exactly as a written one is.

use super::*;
use crate::surface::generics::{TypeSubstitution, unify_click_type};
use crate::surface::scoped_names::Scope;

/// The signature of a pure function, predicate or theorem, as inference
/// reads it.
struct Signature {
    type_parameters: Vec<String>,
    parameters: Vec<ClickType>,
    result: Option<ClickType>,
}

impl Signature {
    fn new(type_parameters: &[String], parameters: &[FunctionParameter]) -> Self {
        Self {
            type_parameters: type_parameters.to_vec(),
            parameters: parameters
                .iter()
                .map(FunctionParameter::click_type_with_object_class)
                .collect(),
            result: None,
        }
    }
}

/// Which signature table a call's name is read from.
#[derive(Clone, Copy)]
pub(super) enum CallKind {
    Function,
    Predicate,
    Theorem,
}

/// What inference reads: each datatype's definition, each signature, and
/// the types of the names in scope. `None` for a name marks a binder that
/// shadows an outer name with a type inference does not know.
pub(super) struct ConstructorTypes {
    datatypes: BTreeMap<String, AlgebraicTypeDefinition>,
    functions: BTreeMap<String, Signature>,
    predicates: BTreeMap<String, Signature>,
    theorems: BTreeMap<String, Signature>,
    /// Each library type's methods: the Click library functions over it,
    /// by the type's name, the method's name and its argument count. A name
    /// two library functions share is ambiguous and maps to `None`.
    methods: BTreeMap<(String, String, usize), Option<String>>,
    variables: std::cell::RefCell<ScopedBinders<Option<ClickType>>>,
    /// Whether any datatype takes type arguments; without one there is
    /// nothing to infer and every hook returns at once.
    active: bool,
}

impl ConstructorTypes {
    pub(super) fn new<'a>(
        datatypes: impl IntoIterator<Item = &'a AlgebraicTypeDefinition>,
        functions: impl IntoIterator<Item = &'a ClickFunctionDefinition>,
        predicates: impl IntoIterator<Item = &'a PredicateDefinition>,
        theorems: impl IntoIterator<Item = &'a TheoremDefinition>,
    ) -> Self {
        let datatypes = datatypes
            .into_iter()
            .map(|definition| (definition.name().to_string(), definition.clone()))
            .collect::<BTreeMap<_, _>>();
        let active = datatypes
            .values()
            .any(|definition| !definition.type_parameters().is_empty());
        if !active {
            return Self::inactive();
        }
        let functions = functions
            .into_iter()
            .map(|definition| {
                let mut signature =
                    Signature::new(definition.type_parameters(), definition.parameters());
                signature.result = Some(definition.return_type_with_object_class());
                (definition.name().to_string(), signature)
            })
            .collect::<BTreeMap<_, _>>();
        let mut methods = BTreeMap::new();
        for (name, signature) in &functions {
            if let Some(module_function) = name.strip_prefix("click::")
                && let Some((_, method)) = module_function.rsplit_once("::")
                && let Some(ClickType::Algebraic(first)) = signature.parameters.first()
            {
                methods
                    .entry((
                        first.name.clone(),
                        method.to_string(),
                        signature.parameters.len() - 1,
                    ))
                    .and_modify(|function: &mut Option<String>| *function = None)
                    .or_insert_with(|| Some(name.clone()));
            }
        }
        Self {
            datatypes,
            functions,
            methods,
            predicates: predicates
                .into_iter()
                .map(|definition| {
                    (
                        definition.name().to_string(),
                        Signature::new(definition.type_parameters(), definition.parameters()),
                    )
                })
                .collect(),
            theorems: theorems
                .into_iter()
                .map(|definition| {
                    (
                        definition.name().to_string(),
                        Signature::new(definition.type_parameters(), definition.parameters()),
                    )
                })
                .collect(),
            variables: Default::default(),
            active,
        }
    }

    pub(super) fn inactive() -> Self {
        Self {
            datatypes: BTreeMap::new(),
            functions: BTreeMap::new(),
            predicates: BTreeMap::new(),
            theorems: BTreeMap::new(),
            methods: BTreeMap::new(),
            variables: Default::default(),
            active: false,
        }
    }

    /// Begin a declaration whose parameters are `parameters`.
    pub(super) fn enter_declaration(
        &self,
        parameters: impl IntoIterator<Item = (String, ClickType)>,
    ) {
        if !self.active {
            return;
        }
        self.variables.borrow_mut().reset(
            parameters
                .into_iter()
                .map(|(name, click_type)| (name, Some(click_type))),
        );
    }

    /// Bind `name` to `click_type` for a nested scope, `None` when its type
    /// is not known, returning the scope it ends with [`Self::restore`].
    pub(super) fn bind(
        &self,
        name: impl Into<SurfaceBinder>,
        click_type: Option<ClickType>,
    ) -> Scope {
        let mut variables = self.variables.borrow_mut();
        let scope = variables.scope();
        if self.active {
            variables.bind(name, click_type);
        }
        scope
    }

    /// End the bindings made since `scope`.
    pub(super) fn restore(&self, scope: Scope) {
        self.variables.borrow_mut().end(scope);
    }

    /// Whether `application` names a generic datatype and leaves out its
    /// type arguments.
    fn unapplied(&self, application: &AlgebraicTypeApplication) -> bool {
        !application.rigid
            && application.arguments.is_empty()
            && self
                .datatypes
                .get(&application.name)
                .is_some_and(|definition| !definition.type_parameters().is_empty())
    }

    /// Whether `expression` still has an unapplied constructor in a
    /// position whose type is the expression's own.
    fn pending(&self, expression: &SyntaxTerm) -> bool {
        match expression {
            SyntaxTerm::AlgebraicConstructor { algebraic_type, .. } => {
                self.unapplied(algebraic_type)
            }
            SyntaxTerm::If {
                then_branch,
                else_branch,
                ..
            } => self.pending(then_branch) || self.pending(else_branch),
            SyntaxTerm::AlgebraicMatch { arms, .. } => {
                arms.iter().any(|arm| self.pending(&arm.body))
            }
            SyntaxTerm::Let { body, .. } => self.pending(body),
            SyntaxTerm::Old(inner)
            | SyntaxTerm::Exact(inner)
            | SyntaxTerm::At {
                expression: inner, ..
            } => self.pending(inner),
            _ => false,
        }
    }

    /// The type `expression` has without looking at its surroundings, when
    /// inference can read it off directly.
    fn known_type(&self, expression: &SyntaxTerm) -> Option<ClickType> {
        if let Some(id) = expression.generated_binder() {
            return self.variables.borrow().get(&id).cloned().flatten();
        }
        match expression {
            SyntaxTerm::IntegerContext(_) => Some(ClickType::Integer),
            SyntaxTerm::AlgebraicConstructor { algebraic_type, .. }
            | SyntaxTerm::AlgebraicVariable { algebraic_type, .. } => (!self
                .unapplied(algebraic_type))
            .then(|| ClickType::Algebraic(algebraic_type.clone())),
            SyntaxTerm::ResourceField(access) => access.click_type.clone(),
            SyntaxTerm::Binding(name)
            | SyntaxTerm::ProgramBinding(name)
            | SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => self.variables.borrow().get(name).cloned().flatten(),
            SyntaxTerm::Old(inner)
            | SyntaxTerm::Exact(inner)
            | SyntaxTerm::At {
                expression: inner, ..
            } => self.known_type(inner),
            SyntaxTerm::If {
                then_branch,
                else_branch,
                ..
            } => self
                .known_type(then_branch)
                .or_else(|| self.known_type(else_branch)),
            // A tuple projection, `t.1`, has its component's type.
            SyntaxTerm::AlgebraicMatch { scrutinee, arms } => {
                let index = crate::surface::tuples::projected_index(arms)?;
                match self.known_type(scrutinee)? {
                    ClickType::Algebraic(application)
                        if crate::surface::tuples::arity(&application.name).is_some() =>
                    {
                        application.arguments.get(index).cloned()
                    }
                    _ => None,
                }
            }
            SyntaxTerm::Call { name, arguments } => {
                let signature = self.functions.get(name)?;
                let result = signature.result.as_ref()?;
                if signature.type_parameters.is_empty() {
                    return Some(result.clone());
                }
                let substitution = self.call_substitution(signature, arguments);
                instantiate(result, &signature.type_parameters, &substitution)
            }
            _ => None,
        }
    }

    /// What the known argument types fix of a generic signature's type
    /// parameters. A conflict fixes nothing: validation reports it.
    fn call_substitution(
        &self,
        signature: &Signature,
        arguments: &[SyntaxTerm],
    ) -> TypeSubstitution {
        let allowed = signature
            .type_parameters
            .iter()
            .map(String::as_str)
            .collect::<BTreeSet<_>>();
        let mut substitution = TypeSubstitution::new();
        for (parameter, argument) in signature.parameters.iter().zip(arguments) {
            if let Some(actual) = self.known_type(argument)
                && unify_click_type(parameter, &actual, &allowed, &mut substitution).is_err()
            {
                return TypeSubstitution::new();
            }
        }
        substitution
    }

    /// Fill in an unapplied constructor's type arguments from its own
    /// arguments, then push field types into arguments that are still
    /// unapplied. Called once per constructor, after its arguments.
    pub(super) fn resolve_constructor(&self, expression: &mut SyntaxTerm) {
        if !self.active {
            return;
        }
        let SyntaxTerm::AlgebraicConstructor {
            algebraic_type,
            variant,
            arguments,
        } = expression
        else {
            return;
        };
        if self.unapplied(algebraic_type) {
            let Some(definition) = self.datatypes.get(&algebraic_type.name) else {
                return;
            };
            let Some(fields) = variant_fields(definition, variant, arguments.len()) else {
                return;
            };
            let parameters = definition.type_parameters();
            let pattern = AlgebraicTypeApplication {
                rigid: false,
                name: algebraic_type.name.clone(),
                arguments: parameters
                    .iter()
                    .map(|parameter| ClickType::Parameter(parameter.clone()))
                    .collect(),
            };
            let allowed = parameters
                .iter()
                .map(String::as_str)
                .collect::<BTreeSet<_>>();
            let mut substitution = TypeSubstitution::new();
            for (field, argument) in fields.iter().zip(arguments.iter()) {
                let (Ok(field), Some(actual)) = (
                    instantiate_field_type(definition, &pattern, field),
                    self.known_type(argument),
                ) else {
                    continue;
                };
                if unify_click_type(&field, &actual, &allowed, &mut substitution).is_err() {
                    return;
                }
            }
            let Some(inferred) = parameters
                .iter()
                .map(|parameter| {
                    substitution
                        .get(parameter)
                        .and_then(|argument| argument.value())
                        .cloned()
                })
                .collect::<Option<Vec<_>>>()
            else {
                return;
            };
            algebraic_type.arguments = inferred;
        }
        self.push_into_fields(algebraic_type, variant, arguments);
    }

    fn push_into_fields(
        &self,
        application: &AlgebraicTypeApplication,
        variant: &str,
        arguments: &mut [SyntaxTerm],
    ) {
        if !arguments.iter().any(|argument| self.pending(argument)) {
            return;
        }
        let Some(definition) = self.datatypes.get(&application.name) else {
            return;
        };
        let Some(fields) = variant_fields(definition, variant, arguments.len()) else {
            return;
        };
        for (field, argument) in fields.iter().zip(arguments.iter_mut()) {
            if self.pending(argument)
                && let Ok(expected) = instantiate_field_type(definition, application, field)
            {
                self.push_expected(argument, &expected);
            }
        }
    }

    /// Give the unapplied constructors in `expression`'s own result
    /// positions the type `expected`.
    pub(super) fn push_expected(&self, expression: &mut SyntaxTerm, expected: &ClickType) {
        if !self.active {
            return;
        }
        let ClickType::Algebraic(expected_application) = expected else {
            return;
        };
        match expression {
            SyntaxTerm::AlgebraicConstructor {
                algebraic_type,
                variant,
                arguments,
            } => {
                if self.unapplied(algebraic_type) {
                    let arity = self
                        .datatypes
                        .get(&algebraic_type.name)
                        .map_or(0, |definition| definition.type_parameters().len());
                    if expected_application.rigid
                        || expected_application.name != algebraic_type.name
                        || expected_application.arguments.len() != arity
                    {
                        return;
                    }
                    algebraic_type
                        .arguments
                        .clone_from(&expected_application.arguments);
                }
                self.push_into_fields(algebraic_type, variant, arguments);
            }
            SyntaxTerm::If {
                then_branch,
                else_branch,
                ..
            } => {
                self.push_expected(then_branch, expected);
                self.push_expected(else_branch, expected);
            }
            SyntaxTerm::AlgebraicMatch { arms, .. } => {
                for arm in arms {
                    self.push_expected(&mut arm.body, expected);
                }
            }
            SyntaxTerm::Let { body, .. } => self.push_expected(body, expected),
            SyntaxTerm::Old(inner)
            | SyntaxTerm::Exact(inner)
            | SyntaxTerm::At {
                expression: inner, ..
            } => self.push_expected(inner, expected),
            _ => {}
        }
    }

    /// Push each parameter type of `name`'s signature into the call
    /// arguments still unapplied, once the other arguments fix it.
    pub(super) fn resolve_call(&self, kind: CallKind, name: &str, arguments: &mut [SyntaxTerm]) {
        if !self.active || !arguments.iter().any(|argument| self.pending(argument)) {
            return;
        }
        let table = match kind {
            CallKind::Function => &self.functions,
            CallKind::Predicate => &self.predicates,
            CallKind::Theorem => &self.theorems,
        };
        let Some(signature) = table.get(name) else {
            return;
        };
        let substitution = if signature.type_parameters.is_empty() {
            TypeSubstitution::new()
        } else {
            self.call_substitution(signature, arguments)
        };
        for (parameter, argument) in signature.parameters.iter().zip(arguments.iter_mut()) {
            if self.pending(argument)
                && let Some(expected) =
                    instantiate(parameter, &signature.type_parameters, &substitution)
            {
                self.push_expected(argument, &expected);
            }
        }
    }

    /// The library function a method of `type_name` names: the function of
    /// the Click library called `method` whose first parameter is a
    /// `type_name` and which takes `arguments` more. A library type's
    /// methods are its library module's functions over it, so a new type
    /// brings its methods with its functions, and a program's own pure
    /// functions are not methods. One lookup in the index built with the
    /// signatures.
    fn library_method(&self, type_name: &str, method: &str, arguments: usize) -> Option<&str> {
        self.methods
            .get(&(type_name.to_string(), method.to_string(), arguments))?
            .as_deref()
    }

    /// The method call `receiver.method(arguments)` as what it means for
    /// the receiver's type (`design/typed-method-resolution.md`): a slice's
    /// `len()` is `slice::len(receiver)`, its `[i]` a read through
    /// `slice::as_ptr(receiver)`, and its `[a..b]` `slice::subslice(receiver,
    /// a, b)`. A receiver
    /// whose type has no such method is refused with the type and method.
    pub(super) fn resolve_method(
        &self,
        receiver: SyntaxTerm,
        method: &str,
        arguments: Vec<SyntaxTerm>,
    ) -> Result<SyntaxTerm, ClickError> {
        let receiver_type = self.known_type(&receiver);
        // A tuple projection, `t.1` (`design/tuples.md`).
        if let Some(index) = crate::surface::tuples::projection_method_index(method) {
            let written = crate::surface::diagnostics::describe_contract_expression(&receiver);
            let arity = match &receiver_type {
                Some(ClickType::Algebraic(application)) => {
                    crate::surface::tuples::arity(&application.name)
                }
                _ => None,
            };
            return match &receiver_type {
                Some(click_type) if arity.is_some() => {
                    let arity = arity.expect("checked above");
                    if index < arity {
                        Ok(crate::surface::tuples::projection(receiver, arity, index))
                    } else {
                        Err(ClickError::new(format!(
                            "`{written}{method}`: the tuple type `{}` has no component {index}",
                            super::describe_click_type(click_type)
                        )))
                    }
                }
                Some(click_type) => Err(ClickError::new(format!(
                    "`{written}{method}`: `{}` is not a tuple, so it has no component {index}",
                    super::describe_click_type(click_type)
                ))),
                None => Err(ClickError::new(format!(
                    "`{written}{method}`: the type of `{written}` is not known here, so its \
                     component {index} cannot be selected; a projection applies to a tuple"
                ))),
            };
        }
        // A string slice's methods are `str`'s: its length, data pointer and
        // bytes, and nothing else a byte slice has.
        if receiver_type
            == Some(ClickType::Program(InterfaceType::Slice(
                crate::kernel::SliceElement::Str,
            )))
            && let Some(resolved) = str_method(receiver.clone(), method, &arguments)
        {
            return Ok(resolved);
        }
        // A slice, or a slice built from its parts whether or not its element
        // type is known here.
        let slice_type = matches!(
            &receiver_type,
            Some(ClickType::Program(InterfaceType::Slice(element)))
                if *element != crate::kernel::SliceElement::Str
        ) || slice_parts(&receiver).is_some();
        if slice_type
            && let Some(resolved) = slice_method(receiver.clone(), method, arguments.clone())
        {
            return Ok(resolved);
        }
        if let Some(ClickType::Algebraic(application)) = &receiver_type {
            // A vector's index `v[i]` is `vec::get(v, i)`, as Rust's `Index`.
            if application.name == "Vec"
                && method == "[]"
                && let [index] = arguments.as_slice()
            {
                return Ok(SyntaxTerm::Call {
                    name: "click::rust::vec::get".to_string(),
                    arguments: vec![receiver, index.clone()],
                });
            }
            // Any other method is the library function of that name over
            // the receiver's type: `v.len()` is `vec::len(v)`.
            if let Some(function) = self.library_method(&application.name, method, arguments.len())
            {
                return Ok(SyntaxTerm::Call {
                    name: function.to_string(),
                    arguments: std::iter::once(receiver).chain(arguments).collect(),
                });
            }
        }
        // An index on a value of another type, such as a sequence, keeps
        // the index it always was.
        if method == "[]"
            && let [index] = arguments.as_slice()
            && !matches!(
                &receiver_type,
                Some(ClickType::Algebraic(_) | ClickType::Program(InterfaceType::Slice(_)))
            )
        {
            return Ok(SyntaxTerm::Index(
                Box::new(receiver),
                Box::new(index.clone()),
            ));
        }
        let written =
            crate::surface::diagnostics::describe_contract_expression(&SyntaxTerm::MethodCall {
                receiver: Box::new(receiver),
                method: method.to_string(),
                arguments,
            });
        Err(ClickError::new(match receiver_type {
            Some(click_type) => format!(
                "`{written}`: `{}` has no method `{method}`",
                super::describe_click_type(&click_type)
            ),
            None => format!(
                "`{written}`: the receiver's type is not known here, so its method `{method}` \
                 cannot be resolved; a method applies to a value of a Click type, such as a slice"
            ),
        }))
    }

    /// An unapplied side of a comparison takes the other side's type.
    pub(super) fn resolve_comparison(&self, left: &mut SyntaxTerm, right: &mut SyntaxTerm) {
        if !self.active {
            return;
        }
        if self.pending(left) {
            if let Some(expected) = self.known_type(right) {
                self.push_expected(left, &expected);
            }
        } else if self.pending(right)
            && let Some(expected) = self.known_type(left)
        {
            self.push_expected(right, &expected);
        }
    }

    /// The types of a match arm's bindings, when the scrutinee's type is
    /// known; an unknown binding shadows whatever the name meant outside.
    pub(super) fn arm_binding_types(
        &self,
        scrutinee: &SyntaxTerm,
        arm: &AlgebraicMatchArm,
    ) -> Vec<Option<ClickType>> {
        let scrutinee = if self.active {
            self.known_type(scrutinee)
        } else {
            None
        };
        self.variant_binding_types(scrutinee.as_ref(), &arm.variant, arm.bindings.len())
    }

    /// The types of a proof `match` or `induct` arm's bindings.
    pub(super) fn proof_arm_binding_types(
        &self,
        scrutinee: Option<&ClickType>,
        arm: &ProofInductionArm,
    ) -> Vec<Option<ClickType>> {
        self.variant_binding_types(scrutinee, &arm.variant, arm.bindings.len())
    }

    /// The type of the scrutinee of a proof `match`.
    pub(super) fn scrutinee_type(&self, scrutinee: &SyntaxTerm) -> Option<ClickType> {
        if !self.active {
            return None;
        }
        self.known_type(scrutinee)
    }

    fn variant_binding_types(
        &self,
        scrutinee: Option<&ClickType>,
        variant: &str,
        arity: usize,
    ) -> Vec<Option<ClickType>> {
        let unknown = || vec![None; arity];
        let Some(ClickType::Algebraic(application)) = scrutinee else {
            return unknown();
        };
        let Some(definition) = self.datatypes.get(&application.name) else {
            return unknown();
        };
        let Some(fields) = variant_fields(definition, variant, arity) else {
            return unknown();
        };
        fields
            .iter()
            .map(|field| instantiate_field_type(definition, application, field).ok())
            .collect()
    }

    /// Bind each of `names` to its type for the scope `body` expands,
    /// then restore what the names meant outside.
    pub(super) fn with_bindings<T, N: Clone + Into<SurfaceBinder>>(
        &self,
        names: &[N],
        types: Vec<Option<ClickType>>,
        body: impl FnOnce() -> T,
    ) -> T {
        let scope = self.variables.borrow().scope();
        for (name, click_type) in names.iter().zip(types) {
            let _ = self.bind(name.clone(), click_type);
        }
        let result = body();
        self.restore(scope);
        result
    }

    /// The type of `expression` for a `let` binding it initializes.
    pub(super) fn binding_type(&self, expression: &SyntaxTerm) -> Option<ClickType> {
        if !self.active {
            return None;
        }
        self.known_type(expression)
    }
}

fn variant_fields<'a>(
    definition: &'a AlgebraicTypeDefinition,
    variant: &str,
    arity: usize,
) -> Option<&'a [AlgebraicFieldType]> {
    definition
        .variants()
        .iter()
        .find(|candidate| candidate.name() == variant)
        .map(AlgebraicVariantDefinition::fields)
        .filter(|fields| fields.len() == arity)
}

/// `click_type` with the signature's own type parameters replaced, or
/// `None` while one of them is still unknown. Any other type parameter is
/// the enclosing declaration's own and stays as it is.
fn instantiate(
    click_type: &ClickType,
    parameters: &[String],
    substitution: &TypeSubstitution,
) -> Option<ClickType> {
    match click_type {
        ClickType::Parameter(name) if parameters.contains(name) => substitution
            .get(name)
            .and_then(|argument| argument.value())
            .cloned(),
        ClickType::Algebraic(application) => Some(ClickType::Algebraic(AlgebraicTypeApplication {
            rigid: application.rigid,
            name: application.name.clone(),
            arguments: application
                .arguments
                .iter()
                .map(|argument| instantiate(argument, parameters, substitution))
                .collect::<Option<Vec<_>>>()?,
        })),
        other => Some(other.clone()),
    }
}

/// The refusal for a constructor whose type arguments nothing fixed.
pub(in crate::surface) fn unapplied_constructor_message(
    datatype: &str,
    variant: &str,
    type_parameters: &[String],
) -> String {
    if crate::surface::tuples::arity(datatype).is_some() {
        return "cannot infer the type of a tuple: neither its components nor the type its \
                position expects fix every component's type; give it one, as in \
                `let t: (int32, int32) = (1, 2); ...`"
            .to_string();
    }
    let parameters = type_parameters.join(", ");
    format!(
        "cannot infer the type arguments of `{datatype}::{variant}`: neither its arguments nor the type its position expects fix `{parameters}`; write them, as in `{datatype}<...>::{variant}`"
    )
}

/// The data pointer and length a slice built from its parts was built
/// with: a `slice::from_raw_parts(p, n)` call.
fn slice_parts(receiver: &SyntaxTerm) -> Option<(&SyntaxTerm, &SyntaxTerm)> {
    match receiver {
        SyntaxTerm::Call { name, arguments }
            if matches!(
                name.as_str(),
                "slice::from_raw_parts" | crate::surface::RUST_SLICE_FROM_RAW_PARTS
            ) =>
        {
            match arguments.as_slice() {
                [pointer, length] => Some((pointer, length)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// A `str` method on `receiver`, a string slice (`design/rust-slice-values.md`,
/// "String slices"): `len()` and `as_ptr()` are its components and
/// `as_bytes()` its bytes as a byte slice. `None` for any other method,
/// including an index, which Rust's `str` has not.
fn str_method(receiver: SyntaxTerm, method: &str, arguments: &[SyntaxTerm]) -> Option<SyntaxTerm> {
    let name = match (method, arguments) {
        ("len", []) => crate::surface::RUST_STR_LEN,
        ("as_ptr", []) => crate::surface::RUST_STR_AS_PTR,
        ("as_bytes", []) => crate::surface::RUST_STR_AS_BYTES,
        _ => return None,
    };
    Some(SyntaxTerm::Call {
        name: name.to_string(),
        arguments: vec![receiver],
    })
}

/// A slice method on `receiver`, a slice (`design/rust-slice-values.md`):
/// `len()` and `as_ptr()` are its components, `[i]` a read through its data
/// pointer, and a range index the subslice `slice::subslice(receiver, a,
/// b)`.
fn slice_method(
    receiver: SyntaxTerm,
    method: &str,
    arguments: Vec<SyntaxTerm>,
) -> Option<SyntaxTerm> {
    let call = |name: &str, arguments| SyntaxTerm::Call {
        name: name.to_string(),
        arguments,
    };
    // A constructed slice's components are its data and its length, so a
    // method on one reads them as written.
    let (pointer, length) = match slice_parts(&receiver) {
        Some((pointer, length)) => (pointer.clone(), length.clone()),
        None => (
            call(crate::surface::RUST_SLICE_AS_PTR, vec![receiver.clone()]),
            call(crate::surface::RUST_SLICE_LEN, vec![receiver.clone()]),
        ),
    };
    // A bound is a `usize`, as in Rust.
    let usize_bound = |bound: SyntaxTerm| match &bound {
        SyntaxTerm::IntegerLiteral(text) => text
            .parse::<u64>()
            .map(|value| {
                SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                    crate::kernel::ProgramValue::UInt64(
                        crate::kernel::OldMachineTerm::uint64_constant(value),
                    ),
                ))
            })
            .unwrap_or(bound),
        _ => bound,
    };
    let (start, end) = match (method, arguments.as_slice()) {
        ("len", []) => return Some(length),
        ("as_ptr", []) => return Some(pointer),
        ("[]", [index]) => {
            return Some(SyntaxTerm::Index(
                Box::new(pointer),
                Box::new(index.clone()),
            ));
        }
        ("[..]", []) => (None, None),
        ("[a..]", [start]) => (Some(usize_bound(start.clone())), None),
        ("[..b]", [end]) => (None, Some(usize_bound(end.clone()))),
        ("[a..b]", [start, end]) => (
            Some(usize_bound(start.clone())),
            Some(usize_bound(end.clone())),
        ),
        _ => return None,
    };
    let zero = SyntaxTerm::ProgramExpression(ProgramExpression::Value(
        crate::kernel::ProgramValue::UInt64(crate::kernel::OldMachineTerm::uint64_constant(0)),
    ));
    Some(call(
        crate::surface::RUST_SUBSLICE,
        vec![receiver, start.unwrap_or(zero), end.unwrap_or(length)],
    ))
}
