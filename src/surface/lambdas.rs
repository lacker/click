//! Typed specification lambdas elaborate to the existing value language.
//! Applications introduce typed lexical lets, preserving simultaneous argument
//! binding and capture avoidance without adding higher-order kernel search.
use super::*;

/// SymbolicMemory state selection belongs around application, not inside its delayed body.
/// Check source literals too, since declaration aliases may be unused.
pub(super) fn validate_body_state(body: &ContractExpression) -> Result<(), ClickError> {
    if contains_old_expression(body) || contains_at_expression(body) {
        return Err(ClickError::new(
            "specification lambda bodies cannot select retained_states with old or at; select the state at application instead",
        ));
    }
    Ok(())
}

pub(super) fn has_function_parameters(definition: &ClickFunctionDefinition) -> bool {
    definition
        .parameters()
        .iter()
        .any(|parameter| matches!(parameter.click_type(), ClickType::Function { .. }))
}

/// Specialize one selected declaration into typed lexical argument bindings.
/// All captures and simultaneous argument binding use ordinary beta elaboration.
pub(super) fn specialize_call(
    definition: &ClickFunctionDefinition,
    arguments: &[ContractExpression],
) -> Result<Option<ContractExpression>, String> {
    if !has_function_parameters(definition) && definition.return_type() != &ClickType::Proposition {
        return Ok(None);
    }
    for (parameter, argument) in definition.parameters().iter().zip(arguments) {
        if matches!(parameter.click_type(), ClickType::Function { .. }) {
            let value = reduce_head_fully(argument)?;
            let ContractExpression::Lambda {
                parameters, result, ..
            } = value.as_ref()
            else {
                return Err(format!(
                    "function `{}` needs a concrete lambda for `{}`",
                    definition.name(),
                    parameter.name()
                ));
            };
            if signature(parameters, result) != *parameter.click_type() {
                return Err(format!(
                    "function `{}` callback `{}` expects {}",
                    definition.name(),
                    parameter.name(),
                    validation::describe_click_type(parameter.click_type())
                ));
            }
        }
    }
    let body = definition
        .body()
        .ok_or_else(|| format!("function `{}` has no body to specialize", definition.name()))?;
    apply_lambda(
        definition.parameters().iter().map(|parameter| {
            (
                parameter.binding_name(),
                parameter.click_type_with_object_class(),
            )
        }),
        definition.return_type(),
        body,
        arguments,
    )
    .map(Some)
}

pub(super) fn signature(
    parameters: &[(SurfaceBinder, ClickType)],
    result: &ClickType,
) -> ClickType {
    ClickType::Function {
        parameters: parameters.iter().map(|(_, ty)| ty.clone()).collect(),
        result: Box::new(result.clone()),
    }
}

/// Application may already be elaborated into typed argument/result lets
/// when a surrounding proposition alias is substituted.
pub(super) fn is_proposition_value(expression: &ContractExpression) -> bool {
    match expression {
        ContractExpression::Proposition(_) => true,
        ContractExpression::Apply { function, .. } => {
            application_result_type(function) == Ok(ClickType::Proposition)
        }
        ContractExpression::Let {
            name,
            click_type,
            value,
            body,
        } => {
            if body.as_ref() == &name.reference() {
                match click_type {
                    Some(ClickType::Proposition) => true,
                    Some(_) => false,
                    None => is_proposition_value(value),
                }
            } else {
                is_proposition_value(body)
            }
        }
        ContractExpression::At { expression, .. } | ContractExpression::Old(expression) => {
            is_proposition_value(expression)
        }
        _ => false,
    }
}

/// Range predicates use ordinary application under the existing quantifier.
pub(super) fn range_proposition(
    start: ContractExpression,
    end: ContractExpression,
    predicate: ContractExpression,
    all: bool,
) -> ClickProposition {
    let item = SurfaceBinder::fresh();
    let body = Box::new(ClickProposition::Value(ContractExpression::Apply {
        function: Box::new(predicate),
        arguments: vec![item.reference()],
    }));
    if all {
        ClickProposition::RangeAll {
            start,
            end,
            item,
            written_item: Some("item".into()),
            body,
        }
    } else {
        ClickProposition::RangeAny {
            start,
            end,
            item,
            written_item: Some("item".into()),
            body,
        }
    }
}

pub(super) fn range_predicate(proposition: &ClickProposition) -> Option<&ContractExpression> {
    let (item, body) = match proposition {
        ClickProposition::RangeAll { item, body, .. }
        | ClickProposition::RangeAny { item, body, .. } => (item, body),
        _ => return None,
    };
    let ClickProposition::Value(ContractExpression::Apply {
        function,
        arguments,
    }) = body.as_ref()
    else {
        return None;
    };
    let [argument] = arguments.as_slice() else {
        return None;
    };
    if argument != &item.reference() {
        return None;
    }
    (!lowering::contract_expression_referenced_bindings(function).contains(&item.kernel_name()))
        .then_some(function)
}

/// A value-based fold applies its step to the primitive fold's two bound
/// values. Fresh binders keep the step's lexical captures outside that scope.
/// The primitive remains the common lowering target for the older shorthand.
pub(super) fn range_fold(
    start: ContractExpression,
    end: ContractExpression,
    initial: ContractExpression,
    step: ContractExpression,
) -> ContractExpression {
    let accumulator = SurfaceBinder::fresh();
    let item = SurfaceBinder::fresh();
    let body = ContractExpression::Apply {
        function: Box::new(step),
        arguments: vec![accumulator.reference(), item.reference()],
    };
    ContractExpression::RangeFold {
        start: Box::new(start),
        end: Box::new(end),
        initial: Box::new(initial),
        accumulator,
        item,
        body: Box::new(body),
    }
}

/// Recognize the step application without exposing the primitive's binder
/// names in printed source. A legacy body that closes over either binder
/// cannot be moved outside that binder's scope.
pub(super) fn range_fold_step(expression: &ContractExpression) -> Option<&ContractExpression> {
    let ContractExpression::RangeFold {
        accumulator,
        item,
        body,
        ..
    } = expression
    else {
        return None;
    };
    let ContractExpression::Apply {
        function,
        arguments,
    } = body.as_ref()
    else {
        return None;
    };
    let [acc, index] = arguments.as_slice() else {
        return None;
    };
    if acc != &accumulator.reference() || index != &item.reference() {
        return None;
    }
    let names = lowering::contract_expression_referenced_bindings(function);
    (!names.contains(&accumulator.kernel_name()) && !names.contains(&item.kernel_name()))
        .then_some(function)
}

/// Read the explicit result carrier without erasing the caller's Integer
/// scope. Full argument/body checking belongs to scoped expression typing.
pub(super) fn application_result_type(function: &ContractExpression) -> Result<ClickType, String> {
    if let ContractExpression::Lambda { result, .. } = function {
        return Ok(result.clone());
    }
    if let Some(reduced) = reduce_head(function)? {
        return application_result_type(&reduced);
    }
    Err("application expects a specification lambda value".into())
}

/// Expose a value's outer form after elaborating local lambda aliases.
/// Fold-law inspection must see the same body as ordinary value lowering.
pub(super) fn reduce_head_fully(
    expression: &ContractExpression,
) -> Result<std::borrow::Cow<'_, ContractExpression>, String> {
    let mut value = std::borrow::Cow::Borrowed(expression);
    while let Some(reduced) = reduce_head(&value)? {
        value = std::borrow::Cow::Owned(reduced);
    }
    Ok(value)
}

/// Only a literal closure has an executable body in this first slice.
/// Function parameters and opaque function results are a later extension.
pub(super) fn reduce_head(
    expression: &ContractExpression,
) -> Result<Option<ContractExpression>, String> {
    match expression {
        ContractExpression::Let {
            name,
            click_type,
            value,
            body,
        } if *click_type == Some(ClickType::Proposition) || is_proposition_value(value) => {
            lowering::substitute_contract_expression(
                body,
                &BTreeMap::from([(name.clone(), value.as_ref().clone())]),
            )
            .map(Some)
        }
        ContractExpression::Let {
            name,
            click_type,
            value,
            body,
        } if matches!(value.as_ref(), ContractExpression::Lambda { .. }) => {
            let ContractExpression::Lambda {
                parameters, result, ..
            } = value.as_ref()
            else {
                unreachable!()
            };
            if let Some(expected) = click_type {
                let actual = signature(parameters, result);
                if expected != &actual {
                    return Err(format!(
                        "let binding `{name}` expects {}, got {}",
                        validation::describe_click_type(expected),
                        validation::describe_click_type(&actual)
                    ));
                }
            }
            lowering::substitute_contract_expression(
                body,
                &BTreeMap::from([(name.clone(), value.as_ref().clone())]),
            )
            .map(Some)
        }
        ContractExpression::Apply {
            function,
            arguments,
        } => {
            let reduced = reduce_head(function)?;
            let function = reduced.as_ref().unwrap_or(function);
            let ContractExpression::Lambda {
                parameters,
                result,
                body,
            } = function
            else {
                if reduced.is_some() {
                    return Ok(Some(ContractExpression::Apply {
                        function: Box::new(function.clone()),
                        arguments: arguments.clone(),
                    }));
                }
                return Ok(None);
            };
            apply_lambda(
                parameters
                    .iter()
                    .map(|(name, ty)| (name.kernel_name(), ty.clone())),
                result,
                body,
                arguments,
            )
            .map(Some)
        }
        _ => Ok(None),
    }
}

fn apply_lambda(
    parameters: impl ExactSizeIterator<Item = (crate::kernel::BindingName, ClickType)>,
    result: &ClickType,
    body: &ContractExpression,
    arguments: &[ContractExpression],
) -> Result<ContractExpression, String> {
    if parameters.len() != arguments.len() {
        return Err(format!(
            "lambda expects {} arguments, got {}",
            parameters.len(),
            arguments.len()
        ));
    }
    // These are lexical slots, not generative authority. Re-elaborating
    // the same application must preserve its contract identity. Exclude
    // all referenced slots, including nested binders, to avoid capture.
    let mut used = BTreeSet::<lowering::LexicalBinding>::new();
    lowering::collect_contract_expression_referenced_bindings(body, &mut used);
    for argument in arguments {
        lowering::collect_contract_expression_referenced_bindings(argument, &mut used);
    }
    let mut next = 0;
    let mut fresh = || loop {
        let id = crate::kernel::GeneratedBinderId::from_spelling(next);
        next += 1;
        if used.insert(lowering::LexicalBinding(id.binding_name())) {
            break SurfaceBinder::Generated(id);
        }
    };
    let bindings = parameters
        .map(|(name, ty)| (name, fresh(), ty))
        .collect::<Vec<_>>();
    let result_name = fresh();
    let replacements = bindings
        .iter()
        .map(|(old, new, _)| (old.clone(), new.reference()))
        .collect::<BTreeMap<_, _>>();
    let body = lowering::substitute_contract_expression(body, &replacements)?;
    let mut applied = ContractExpression::Let {
        name: result_name.clone(),
        click_type: Some(result.clone()),
        value: Box::new(body),
        body: Box::new(result_name.reference()),
    };
    for ((_, name, ty), argument) in bindings.into_iter().zip(arguments).rev() {
        applied = ContractExpression::Let {
            name,
            click_type: Some(ty),
            value: Box::new(argument.clone()),
            body: Box::new(applied),
        };
    }
    Ok(applied)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn specification_function_parameters_apply_forward_and_expand() {
        let declarations = "function twice(f: fn(Integer) -> Integer, x: Integer) -> Integer { f(f(x)) } function forward(f: fn(Integer) -> Integer, x: Integer) -> Integer { let alias = f; twice(alias, x) }";
        for (name, proof) in [
            (
                "twice",
                "by { unfold(twice(|n: Integer| -> Integer { n + 1 }, 3)); close(); }",
            ),
            (
                "forward",
                "by { unfold(forward(|n: Integer| -> Integer { n + 1 }, 3)); close(); }",
            ),
        ] {
            let source = format!(
                "{declarations} theorem test() {{ ensures {name}(|n: Integer| -> Integer {{ n + 1 }}, 3) == 5 {proof} }}"
            );
            let verified = verify_click_theorems(&source)
                .unwrap_or_else(|error| panic!("{source}: {}", error.report()));
            let expanded = verified[0].expanded_proof_source().unwrap();
            assert!(!expanded.contains("solve("), "{expanded}");
            verify_click_theorems(&source.replace(proof, &expanded))
                .unwrap_or_else(|error| panic!("{expanded}: {}", error.report()));
            assert!(verify_click_theorems(&source.replace("== 5", "== 6")).is_err());
        }
    }

    #[test]
    fn callback_binders_shadow_and_proposition_helpers_expand() {
        let source = "function shadow(f: fn(Integer) -> Integer, x: Integer) -> Integer { (|f: Integer| -> Integer { f + 1 })(x) } theorem test() { ensures shadow(|n: Integer| -> Integer { n }, 3) == 4 by close(); }";
        verify_click_theorems(source).unwrap_or_else(|error| panic!("{}", error.report()));
        for (declaration, statement, proof) in [
            (
                "function every(p: fn(int32) -> Prop, lo: int32, hi: int32) -> Prop { (lo..hi).all(p) }",
                "every(|i: int32| -> Prop { i < hi }, lo, hi)",
                "by { intro(); intro(); close(); }",
            ),
            (
                "function some(p: fn(int32) -> Prop, lo: int32, hi: int32) -> Prop { (lo..hi).any(p) }",
                "some(|i: int32| -> Prop { i == lo }, lo, hi)",
                "by { witness(lo); close(); }",
            ),
        ] {
            let source = format!(
                "{declaration} theorem test(lo: int32, hi: int32) {{ requires lo < hi; ensures {statement} {proof} }}"
            );
            let verified = verify_click_theorems(&source)
                .unwrap_or_else(|error| panic!("{source}: {}", error.report()));
            let expanded = verified[0].expanded_proof_source().unwrap();
            assert!(!expanded.contains("solve("), "{expanded}");
            verify_click_theorems(&source.replace(proof, &expanded))
                .unwrap_or_else(|error| panic!("{expanded}: {}", error.report()));
        }
    }

    #[test]
    fn callback_fold_append_and_memory_expansions_recheck() {
        let proof = "by { unfold(total(|acc: Integer, i: int32| -> Integer { acc + to_integer(i) }, lo, hi + 1)); close(); }";
        let source = format!(
            "function total(step: fn(Integer, int32) -> Integer, lo: int32, hi: int32) -> Integer {{ (lo..hi).fold(0, step) }} theorem test(lo: int32, hi: int32) {{ requires lo <= hi; requires hi < 2147483647; ensures total(|acc: Integer, i: int32| -> Integer {{ acc + to_integer(i) }}, lo, hi + 1) == total(|acc: Integer, i: int32| -> Integer {{ acc + to_integer(i) }}, lo, hi) + to_integer(hi) {proof} }}"
        );
        let verified =
            verify_click_theorems(&source).unwrap_or_else(|error| panic!("{}", error.report()));
        let expanded = verified[0].expanded_proof_source().unwrap();
        assert!(!expanded.contains("solve("), "{expanded}");
        verify_click_theorems(&source.replace(proof, &expanded))
            .unwrap_or_else(|error| panic!("{expanded}: {}", error.report()));

        let c = [("write.c", "void write(int32* p) { p[0] = 5; }")];
        let proof = "by { step_until(function.exit); unfold(access(|i: int32| -> Integer { to_integer(p[i]) }, 0)); close(); }";
        let source = format!(
            "verifying \"write.c\"; function access(read: fn(int32) -> Integer, i: int32) -> Integer {{ read(i) }} void write(int32* p) {{ owns p[0..1]; requires p[0] == 0; ensures access(|i: int32| -> Integer {{ to_integer(p[i]) }}, 0) == 5; }} {proof}"
        );
        let verified =
            verify_c_sources(&source, &c).unwrap_or_else(|error| panic!("{}", error.report()));
        let expanded = verified[0].expanded_proof_source().unwrap();
        assert!(!expanded.contains("solve("), "{expanded}");
        verify_c_sources(&source.replace(proof, &expanded), &c)
            .unwrap_or_else(|error| panic!("{expanded}: {}", error.report()));
    }

    #[test]
    fn callbacks_preserve_algebraic_arguments_and_results() {
        let declarations = "spec enum Boxed { Value(Integer) } function wrap(f: fn(Integer) -> Integer, x: Integer) -> Boxed { Boxed::Value(f(x)) } function accepts(p: fn(Integer) -> Prop, b: Boxed) -> Prop { b == Boxed::Value(4) and p(4) }";
        for (statement, proof) in [
            (
                "wrap(|x: Integer| -> Integer { x + 1 }, 3) == Boxed::Value(4)",
                "by { unfold(wrap(|x: Integer| -> Integer { x + 1 }, 3)); have to_integer(3) + 1 == 4 by close(); close(); }",
            ),
            (
                "accepts(|x: Integer| -> Prop { x == 4 }, Boxed::Value(4))",
                "by close();",
            ),
        ] {
            let source = format!("{declarations} theorem test() {{ ensures {statement} {proof} }}");
            let verified = verify_click_theorems(&source)
                .unwrap_or_else(|error| panic!("{source}: {}", error.report()));
            let expanded = verified[0].expanded_proof_source().unwrap();
            assert!(!expanded.contains("solve("), "{expanded}");
            verify_click_theorems(&source.replace(proof, &expanded))
                .unwrap_or_else(|error| panic!("{expanded}: {}", error.report()));
        }
    }

    #[test]
    fn specification_callback_signatures_are_checked_even_when_unused() {
        for source in [
            "function bad(f: fn(Integer) -> Integer) -> Integer { f(true) }",
            "function bad() -> Prop { missing == 0 }",
            "function bad(f: fn(Integer) -> Integer) -> Integer { f(1, 2) }",
            "function bad(f: fn(Integer) -> Integer) -> Integer { f + 1 }",
            "function bad(f: fn(Integer) -> Integer) -> Bool { f(1) }",
            "function bad(f: fn(Integer) -> Integer) -> Integer { let unused = |n: Integer| -> Integer { f(true) }; 0 }",
            "function bad(f: fn(fn(Integer) -> Integer) -> Integer) -> Integer { 0 }",
            "theorem bad(f: fn(Integer) -> Integer) { ensures true; }",
            "function bad(f: fn(Integer) -> Integer) -> fn(Integer) -> Integer { f }",
            "function use(f: fn(Integer) -> Integer) -> Integer { f(1) } theorem bad() { ensures use(|x: int32| -> int32 { x }) == 1; }",
        ] {
            assert!(parser::parse(source).is_err(), "accepted {source}");
        }
    }

    #[test]
    fn proposition_lambdas_reject_wrong_value_categories_and_signatures() {
        let mut accepted = Vec::new();
        for source in [
            "function bad() -> int32 { let f = |x: int32| -> Prop { x == x }; f(0) + 1 }",
            "function bad() -> int32 { let p: Bool = (|x: int32| -> Prop { x == x })(0); 0 }",
            "theorem bad() { ensures (0..3).all(|x: int32| -> Bool { true }) by close(); }",
            "theorem bad() { ensures (0..3).any(|x: Integer| -> Prop { x == x }) by close(); }",
            "theorem bad() { ensures (0..3).all(|x: int32, y: int32| -> Prop { x == y }) by close(); }",
            "theorem bad() { ensures (|| -> Prop { true })() == true by close(); }",
            "function bad() -> int32 { let unused = |x: int32| -> Prop { x + true == 0 }; 0 }",
        ] {
            if parser::parse(source).is_ok() {
                accepted.push(source);
            }
        }
        assert!(
            accepted.is_empty(),
            "incorrectly accepted: {}",
            accepted.join("\n")
        );
    }

    #[test]
    fn proposition_lambdas_cannot_prove_a_false_application() {
        let source = "theorem bad() { ensures (|x: Integer| -> Prop { x > 0 })(0) by close(); }";
        let error =
            verify_click_theorems(source).expect_err("application preserves the proposition");
        assert_eq!(error.kind(), ClickErrorKind::Proof, "{}", error.report());
    }

    #[test]
    fn proposition_lambda_proofs_expand_and_recheck_without_search() {
        let cases = [
            (
                "theorem test(x: Integer) { let p = |n: Integer| -> Prop { n == n }; let claim = p(x); ensures claim by close(); }",
                "by close();",
            ),
            (
                "function captured(limit: int32, value: int32) -> Integer { let p = |x: int32| -> Prop { x < limit }; let limit: int32 = 0; if p(value) { 1 } else { 0 } } theorem test() { ensures captured(5, 3) == 1 by { unfold(captured(5, 3)); close(); } }",
                "by { unfold(captured(5, 3)); close(); }",
            ),
            (
                "theorem test(x: Integer) { let p: fn(Integer) -> Prop = |n: Integer| -> Prop { n == n }; ensures p(x) by close(); }",
                "by close();",
            ),
            (
                "theorem test(x: Integer) { ensures (|n: Integer| -> Prop { forall (y: Integer) { n + y == y + n } })(x) by { intro(); close(); } }",
                "by { intro(); close(); }",
            ),
            (
                "theorem test(lo: int32, hi: int32, limit: int32) { let p = |x: int32| -> Prop { x < limit }; requires hi <= limit; ensures (lo..hi).all(p) by { let k = intro(); intro(); close(); } }",
                "by { let k = intro(); intro(); close(); }",
            ),
            (
                "theorem test(lo: int32, hi: int32) { let p = |x: int32| -> Prop { x == lo }; requires lo < hi; ensures (lo..hi).any(p) by { witness(lo); close(); } }",
                "by { witness(lo); close(); }",
            ),
            (
                "theorem test(p: int32*, lo: int32, hi: int32) { let zero = |i: int32| -> Prop { p[i] == 0 }; requires viewable(p[lo..hi]); requires (lo..hi).all(|i| { p[i] == 0 }); ensures (lo..hi).all(zero) by { let k = intro(); intro(); close(); } }",
                "by { let k = intro(); intro(); close(); }",
            ),
            (
                "theorem test(p: int32*, lo: int32, hi: int32) { let zero = |i: int32| -> Prop { p[i] == 0 }; requires lo < hi; requires viewable(p[lo..hi]); requires p[lo] == 0; ensures (lo..hi).any(zero) by { witness(lo); close(); } }",
                "by { witness(lo); close(); }",
            ),
        ];
        for (source, proof) in cases {
            let verified = verify_click_theorems(source)
                .unwrap_or_else(|error| panic!("{source}: {}", error.report()));
            let expanded = verified[0].expanded_proof_source().unwrap();
            assert!(!expanded.contains("solve("), "{expanded}");
            let rechecked = source.replace(proof, &expanded);
            verify_click_theorems(&rechecked)
                .unwrap_or_else(|error| panic!("{rechecked}: {}", error.report()));
        }
    }

    #[test]
    fn proposition_lambda_source_round_trips() {
        let source = "function test(offset: Integer) -> int32 { let p: fn(Integer) -> Prop = |x: Integer| -> Prop { forall (y: Integer) { x + y == y + x } and x == offset }; 0 }";
        let file = parser::parse(source).unwrap();
        let original = file.click_function_definitions()[0].body().unwrap();
        let printed = diagnostics::describe_contract_expression(original);
        let reparsed = parser::parse(&format!(
            "function test(offset: Integer) -> int32 {{ {printed} }}"
        ))
        .unwrap();
        assert_eq!(
            Some(original),
            reparsed.click_function_definitions()[0].body()
        );
    }

    #[test]
    fn lambda_folds_reject_incompatible_step_signatures() {
        for (step, diagnostic) in [
            ("7", "application expects a specification lambda"),
            (
                "|acc: Integer| -> Integer { acc }",
                "lambda expects 1 arguments",
            ),
            (
                "|acc: Integer, k: Integer| -> Integer { acc + k }",
                "range fold step expects",
            ),
            (
                "|acc: Integer, k: int32| -> int32 { 0 }",
                "range fold step expects",
            ),
            (
                "|acc: uint64, k: int32| -> uint64 { acc }",
                "range fold step expects",
            ),
        ] {
            let source = format!(
                "function bad(lo: int32, hi: int32) -> Integer {{ (lo..hi).fold(0, {step}) }}"
            );
            let error = parser::parse(&source).expect_err(&source);
            assert!(
                error.message().contains(diagnostic),
                "{source}: {}",
                error.message()
            );
        }
        let source = "function bad(lo: int32, hi: int32) -> Integer { (lo..hi).fold(0u64, |acc: Integer, k: int32| -> Integer { acc }) }";
        let error = parser::parse(source).expect_err(source);
        assert!(
            error
                .message()
                .contains("range fold initial value expects Integer"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn lambda_folds_print_step_values_without_primitive_binders() {
        let source = "function total(lo: int32, hi: int32, offset: Integer) -> Integer { let step = |acc: Integer, k: int32| -> Integer { acc + to_integer(k) + offset }; (lo..hi).fold(0, step) }";
        let file = parser::parse(source).unwrap();
        let original = file.click_function_definitions()[0].body().unwrap();
        let body = diagnostics::describe_contract_expression(original);
        assert!(!body.contains("__click_fold_"), "{body}");
        let reparsed = parser::parse(&format!(
            "function total(lo: int32, hi: int32, offset: Integer) -> Integer {{ {body} }}"
        ))
        .unwrap();
        // Value-based fold syntax deliberately elides its primitive binder
        // identities; reparsing allocates alpha-equivalent fresh binders.
        assert_eq!(
            body,
            diagnostics::describe_contract_expression(
                reparsed.click_function_definitions()[0].body().unwrap()
            )
        );
    }

    #[test]
    fn lambda_folds_expand_and_recheck_without_search() {
        let source = "function total(lo: int32, hi: int32) -> Integer { (lo..hi).fold(0, |acc: Integer, k: int32| -> Integer { acc + to_integer(k) }) } theorem empty(n: int32) { ensures total(n, n) == 0 by { have n <= n; unfold(total(n, n)); close(); } }";
        let verified = verify_click_theorems(source).unwrap();
        let expanded = verified[0].expanded_proof_source().unwrap();
        assert!(!expanded.contains("solve("), "{expanded}");
        let rechecked = source.replace(
            "by { have n <= n; unfold(total(n, n)); close(); }",
            &expanded,
        );
        verify_click_theorems(&rechecked)
            .unwrap_or_else(|error| panic!("{rechecked}: {}", error.report()));
    }

    #[test]
    fn lambda_fold_alias_append_expands_and_rechecks_without_search() {
        let proof = "by { unfold(total(lo, hi + 1, offset)); close(); }";
        let source = format!(
            "function total(lo: int32, hi: int32, offset: Integer) -> Integer {{ let step = |acc: Integer, k: int32| -> Integer {{ acc + to_integer(k) + offset }}; let alias = step; (lo..hi).fold(0, alias) }} theorem append(lo: int32, hi: int32, offset: Integer) {{ requires lo <= hi; requires hi < 2147483647; ensures total(lo, hi + 1, offset) == total(lo, hi, offset) + to_integer(hi) + offset {proof} }}"
        );
        let verified = verify_click_theorems(&source).unwrap();
        let expanded = verified[0].expanded_proof_source().unwrap();
        assert!(!expanded.contains("solve("), "{expanded}");
        let rechecked = source.replace(proof, &expanded);
        verify_click_theorems(&rechecked)
            .unwrap_or_else(|error| panic!("{rechecked}: {}", error.report()));
    }

    #[test]
    fn typed_lambdas_reject_invalid_signatures_and_applications() {
        for (expression, diagnostic) in [
            (
                "(|x: Integer| -> Integer { x })(1, 2)",
                "lambda expects 1 arguments",
            ),
            ("(|x: Integer| -> Integer { x })(1u64)", "expects Integer"),
            (
                "(|x: uint64| -> uint64 { x })(to_integer(1))",
                "expects uint64",
            ),
            (
                "(|x: Integer, x: Integer| -> Integer { x })(1, 2)",
                "duplicate lambda parameter",
            ),
            ("(|x| -> Integer { x })(1)", "expected `:`"),
            ("(1)(2)", "application expects a specification lambda"),
            (
                "(|x: int32*| -> int32 { 0 })(0)",
                "lambda parameters and results",
            ),
            (
                "(|x: int32| -> int32 { x })()",
                "lambda expects 1 arguments",
            ),
            (
                "let f = |x: Integer| -> Integer { x }; f",
                "fn(Integer) -> Integer",
            ),
            (
                "let f = |x: int32| -> int32 { 1u64 }; 0",
                "lambda result expects int32",
            ),
            (
                "let f: fn(int32) -> int32 = |x: Integer| -> Integer { x }; 0",
                "expects fn(int32) -> int32",
            ),
        ] {
            let result = if expression.starts_with("(|x: uint64|") {
                "uint64"
            } else {
                "int32"
            };
            let source = format!("function test() -> {result} {{ {expression} }}");
            let error = parser::parse(&source).expect_err(&source);
            assert!(
                error.message().contains(diagnostic),
                "{source}: {}",
                error.message()
            );
        }
    }

    #[test]
    fn typed_lambdas_type_reads_without_requiring_construction_permissions() {
        for body in ["p[x]", "read(p)"] {
            let source = format!(
                "function read(p: int32*) -> int32 {{ p[0] }} function test(p: int32*) -> int32 {{ let unused = |x: int32| -> int32 {{ {body} }}; 0 }}"
            );
            parser::parse(&source).unwrap_or_else(|error| panic!("{source}: {}", error.report()));
        }
        parser::parse("function test(p: int32*) -> int32 { let unused = |x: int32| -> Prop { p[x] == 0 }; 0 }").unwrap();
        assert!(
            parser::parse(
                "function test(p: int32*) -> int32 { let unused = |x: int32| -> Bool { p[x] }; 0 }"
            )
            .is_err()
        );
    }

    #[test]
    fn typed_lambda_expansion_rechecks_without_search() {
        let source =
            "theorem expand() { ensures (|x: Integer| -> Integer { x + 1 })(3) == 4 by close(); }";
        let verified = verify_click_theorems(source).unwrap();
        let expanded = verified[0].expanded_proof_source().unwrap();
        assert!(!expanded.contains("solve("), "{expanded}");
        let rechecked = source.replace("by close();", &expanded);
        verify_click_theorems(&rechecked)
            .unwrap_or_else(|error| panic!("{rechecked}: {}", error.report()));
    }

    #[test]
    fn typed_lambda_application_does_not_prove_a_false_result() {
        let source = "theorem false_result() { ensures (|x: Integer| -> Integer { x + 1 })(3) == 5 by close(); }";
        let error =
            verify_click_theorems(source).expect_err("beta application preserves the lambda body");
        assert_eq!(error.kind(), ClickErrorKind::Proof, "{}", error.report());
    }

    #[test]
    fn typed_lambdas_reject_function_values_used_as_scalars_in_unused_bodies() {
        for (body, diagnostic) in [
            (
                "(|x: int32| -> int32 { x }) + 1",
                "cannot be arithmetic operands",
            ),
            ("~(|x: int32| -> int32 { x })", "cannot be bitwise operands"),
            (
                "identity(|x: int32| -> int32 { x })",
                "got a specification function",
            ),
        ] {
            let source = format!(
                "function identity(x: int32) -> int32 {{ x }} function test() -> int32 {{ let unused = |x: int32| -> int32 {{ {body} }}; 0 }}"
            );
            let error = parser::parse(&source).expect_err("unused lambda bodies remain typed");
            assert!(
                error.message().contains(diagnostic)
                    || error.message().contains("lambda is not a scalar"),
                "{}",
                error.message()
            );
        }
    }

    #[test]
    fn typed_lambdas_refuse_state_selectors_even_when_unused() {
        for body in ["old(p[x])", "at(function.entry, p[x])"] {
            let source = format!(
                "theorem test(p: int32*) {{ let unused = |x: int32| -> int32 {{ {body} }}; ensures true by close(); }}"
            );
            let error = parser::parse(&source)
                .expect_err("body retained_state selection remains explicit at application");
            assert!(
                error
                    .message()
                    .contains("lambda bodies cannot select retained_states"),
                "{}",
                error.report()
            );
        }
        let source = "theorem test(p: int32*) { let unused = |x: int32| -> Prop { at(function.entry, p[x] == 0) }; ensures true by close(); }";
        assert!(parser::parse(source).is_err());
    }

    #[test]
    fn memory_lambda_application_checks_permissions_and_definedness() {
        for (requires, body) in [
            ("", "p[i]"),
            ("requires viewable(p[0..1]);", "p[i + 2147483647]"),
        ] {
            let source = format!(
                "theorem test(p: int32*) {{ {requires} let read = |i: int32| -> int32 {{ {body} }}; ensures defined(read(1)) by close(); }}"
            );
            parser::parse(&source).unwrap();
            let error = verify_click_theorems(&source).expect_err("application owes read validity");
            assert_eq!(error.kind(), ClickErrorKind::Proof, "{}", error.report());
        }
        verify_click_theorems("theorem test(p: int32*) { let read = |i: int32| -> int32 { p[i] }; requires defined(p[1]); ensures defined(read(1)) by close(); }").unwrap();
        verify_click_theorems("theorem test(p: int32*) { let read = |i: int32| -> Integer { to_integer(p[i]) }; requires defined(p[1]); ensures read(1) == to_integer(p[1]) by close(); }").unwrap();
        let c = [("nothing.c", "void test(int32* p) {}")];
        let source = "verifying \"nothing.c\"; void test(int32* p) { let read = |i: int32| -> int32 { p[i] }; views p[0..1]; ensures defined(read(0)); }";
        verify_c_sources(source, &c).unwrap();
        assert!(verify_c_sources(&source.replace("views p[0..1];", ""), &c).is_err());
        let source = "theorem test(p: int32*) { let unused = |i: int32| -> int32 { p[i] }; ensures true by close(); }";
        verify_click_theorems(source).unwrap();
    }

    #[test]
    fn unused_declaration_memory_lambdas_are_still_typed() {
        for prefix in ["theorem test(p: int32*)", "int32 test(int32* p)"] {
            let source =
                format!("{prefix} {{ let unused = |i: int32| -> Bool {{ p[i] }}; ensures true; }}");
            let error = parser::parse(&source)
                .expect_err("unused declarations retain lambda result checks");
            assert!(
                error.message().contains("lambda result expects"),
                "{}",
                error.report()
            );
        }
        let source = "theorem test(p: int32*) { let n: Integer = 1; let unused = |i: int32| -> Integer { n + to_integer(p[i]) }; ensures true by close(); }";
        verify_click_theorems(source).unwrap();
    }

    #[test]
    fn memory_lambda_store_proofs_expand_and_recheck() {
        let c = [("write.c", "void write(int32* p) { p[0] = 5; }")];
        for body in ["p[i] == 5", "to_integer(p[i]) == 5"] {
            let source = format!(
                "verifying \"write.c\"; void write(int32* p) {{ let read = |i: int32| -> Prop {{ {body} }}; owns p[0..1]; requires p[0] == 0; ensures read(0); }} by {{ step_until(function.exit); close(); }}"
            );
            let verified = verify_c_sources(&source, &c)
                .unwrap_or_else(|error| panic!("{source}: {}", error.report()));
            let expanded = verified[0].expanded_proof_source().unwrap();
            assert!(!expanded.contains("solve("), "{expanded}");
            verify_c_sources(
                &source.replace("by { step_until(function.exit); close(); }", &expanded),
                &c,
            )
            .unwrap_or_else(|error| panic!("{expanded}: {}", error.report()));
            assert!(
                verify_c_sources(&source.replace("== 5", "== 0"), &c).is_err(),
                "a store must invalidate the old value"
            );
        }
    }

    #[test]
    fn typed_lambda_printing_round_trips() {
        let source = "function test(n: Integer) -> Integer { let f: fn(Integer) -> Integer = |x: Integer| -> Integer { x + n }; f(3) }";
        let file = parser::parse(source).unwrap();
        let body = diagnostics::describe_contract_expression(
            file.click_function_definitions()[0].body().unwrap(),
        );
        let reparsed = parser::parse(&format!(
            "function test(n: Integer) -> Integer {{ {body} }}"
        ))
        .unwrap();
        assert_eq!(
            file.click_function_definitions()[0].body(),
            reparsed.click_function_definitions()[0].body()
        );
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../scaling_tests/surface/lambdas.rs");
}
