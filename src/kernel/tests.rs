use super::*;
use std::collections::HashSet;

fn lambda(parameter: Symbol, body: Computation) -> Computation {
    Computation::Lambda(Lambda {
        parameter,
        body: Box::new(body),
    })
}

fn apply(function: Computation, argument: Computation) -> Computation {
    Computation::Apply {
        function: Box::new(function),
        argument: Box::new(argument),
    }
}

fn cons(head: Computation, tail: Computation) -> Computation {
    Computation::Cons {
        head: Box::new(head),
        tail: Box::new(tail),
    }
}

fn head(computation: Computation) -> Computation {
    Computation::Head(Box::new(computation))
}

fn tail(computation: Computation) -> Computation {
    Computation::Tail(Box::new(computation))
}

fn list_case(
    list: Computation,
    nil: Computation,
    cons_var: Symbol,
    cons_case: Computation,
) -> Computation {
    Computation::ListCase(ListCase {
        list: Box::new(list),
        nil: Box::new(nil),
        cons: cons_var,
        cons_case: Box::new(cons_case),
    })
}

fn if_computation(
    condition: Computation,
    then_branch: Computation,
    else_branch: Computation,
) -> Computation {
    if_then_else(condition, then_branch, else_branch)
}

fn symbol_eq_computation(left: Computation, right: Computation) -> Computation {
    symbol_eq(left, right)
}

fn value_kind_computation(computation: Computation) -> Computation {
    value_kind(computation)
}

fn error(error: ErrorName) -> Computation {
    Computation::Error(error)
}

#[test]
fn computations_classify_values_effects_and_outcomes() {
    let value_computation = cons(Computation::Quote(Symbol(1)), Computation::Nil);
    let value = Value::cons(Value::quote(Symbol(1)), ListValue::nil());
    let error_computation = error(ErrorName(2));
    let pending_computation = apply(
        lambda(Symbol(1), Computation::Var(Symbol(1))),
        Computation::Nil,
    );

    assert_eq!(value_computation.as_value(), Some(value.clone()));
    assert_eq!(
        error_computation.as_effect(),
        Some(Effect::Error(ErrorName(2)))
    );
    assert_eq!(
        Computation::Diverge.as_outcome(),
        Some(Outcome::Effect(Effect::Diverge))
    );
    assert_eq!(pending_computation.as_outcome(), None);
    assert_eq!(
        normal_outcome(&pending_computation),
        Some(Outcome::Value(Value::nil()))
    );
    assert_eq!(normal_outcome(&Computation::Var(Symbol(3))), None);
    assert_eq!(value.into_computation(), value_computation);
}

#[test]
fn alpha_eq_prop_renames_bound_variables_only() {
    let left = forall(
        Symbol(1),
        exists(
            Symbol(2),
            equal(Computation::Var(Symbol(1)), Computation::Var(Symbol(2))),
        ),
    );
    let right = forall(
        Symbol(10),
        exists(
            Symbol(11),
            equal(Computation::Var(Symbol(10)), Computation::Var(Symbol(11))),
        ),
    );

    assert!(alpha_eq_prop(&left, &right));
    assert!(!alpha_eq_prop(
        &equal(Computation::Var(Symbol(1)), Computation::Var(Symbol(2))),
        &equal(Computation::Var(Symbol(1)), Computation::Var(Symbol(11))),
    ));
}

#[test]
fn alpha_eq_computation_renames_lambda_and_list_case_binders() {
    let left = lambda(
        Symbol(1),
        list_case(
            Computation::Var(Symbol(9)),
            Computation::Nil,
            Symbol(2),
            apply(Computation::Var(Symbol(1)), Computation::Var(Symbol(2))),
        ),
    );
    let right = lambda(
        Symbol(10),
        list_case(
            Computation::Var(Symbol(9)),
            Computation::Nil,
            Symbol(20),
            apply(Computation::Var(Symbol(10)), Computation::Var(Symbol(20))),
        ),
    );
    let reversed = lambda(
        Symbol(10),
        list_case(
            Computation::Var(Symbol(9)),
            Computation::Nil,
            Symbol(20),
            apply(Computation::Var(Symbol(20)), Computation::Var(Symbol(10))),
        ),
    );

    assert!(alpha_eq_computation(&left, &right));
    assert!(!alpha_eq_computation(&left, &reversed));
    assert!(!alpha_eq_computation(
        &lambda(Symbol(1), Computation::Quote(Symbol(1))),
        &lambda(Symbol(2), Computation::Quote(Symbol(2))),
    ));
}

#[test]
fn checker_accepts_alpha_equivalent_goal() {
    let proof = Proof::ForAllIntro {
        variable: Symbol(1),
        proof: Box::new(Proof::Refl(Computation::Var(Symbol(1)))),
    };
    let expected = forall(
        Symbol(2),
        equal(Computation::Var(Symbol(2)), Computation::Var(Symbol(2))),
    );

    assert!(check(&proof, &expected));
}

#[test]
fn step_beta_reduces_after_argument_is_ready() {
    let computation = apply(
        lambda(Symbol(1), Computation::Var(Symbol(1))),
        Computation::Quote(Symbol(2)),
    );

    assert_eq!(
        step(&computation),
        Step::Reduced(Computation::Quote(Symbol(2)))
    );
}

#[test]
fn application_reduces_argument_before_beta() {
    let computation = apply(
        lambda(Symbol(1), Computation::Quote(Symbol(9))),
        apply(
            lambda(Symbol(2), Computation::Var(Symbol(2))),
            Computation::Quote(Symbol(3)),
        ),
    );

    assert_eq!(
        step(&computation),
        Step::Reduced(apply(
            lambda(Symbol(1), Computation::Quote(Symbol(9))),
            Computation::Quote(Symbol(3))
        ))
    );
    assert_eq!(normal_form(&computation), Computation::Quote(Symbol(9)));
}

#[test]
fn lambda_is_a_value_without_evaluating_body() {
    let computation = lambda(
        Symbol(1),
        apply(
            lambda(Symbol(2), Computation::Var(Symbol(2))),
            Computation::Var(Symbol(1)),
        ),
    );

    assert_eq!(step(&computation), Step::Normal);
}

#[test]
fn is_value_distinguishes_values_from_pending_computations() {
    assert!(computation_is_value(&Computation::Nil));
    assert!(computation_is_value(&Computation::Quote(Symbol(1))));
    assert!(computation_is_value(&lambda(
        Symbol(1),
        Computation::Var(Symbol(1))
    )));
    assert!(computation_is_value(&cons(
        Computation::Quote(Symbol(1)),
        Computation::Nil
    )));

    assert!(!computation_is_value(&apply(
        Computation::Var(Symbol(1)),
        Computation::Quote(Symbol(2))
    )));
    assert!(!computation_is_value(&Computation::Diverge));
    assert!(!computation_is_value(&error(ErrorName(1))));
    assert!(!computation_is_value(&Computation::Var(Symbol(1))));
    assert_eq!(step(&Computation::Var(Symbol(1))), Step::Normal);
}

#[test]
fn application_propagates_effects() {
    let thrown = error(ErrorName(1));

    assert_eq!(
        normal_form(&apply(thrown.clone(), Computation::Quote(Symbol(2)))),
        thrown.clone()
    );
    assert_eq!(
        normal_form(&apply(
            lambda(Symbol(1), Computation::Quote(Symbol(2))),
            thrown.clone()
        )),
        thrown
    );
    assert_eq!(
        normal_form(&apply(
            lambda(Symbol(1), Computation::Quote(Symbol(2))),
            Computation::Diverge
        )),
        Computation::Diverge
    );
}

#[test]
fn apply_known_non_callable_reduces_to_error() {
    let computation = apply(Computation::Nil, Computation::Quote(Symbol(2)));

    assert_eq!(step(&computation), Step::Reduced(error(RUNTIME_ERROR)));
}

#[test]
fn cons_evaluates_head_then_tail_and_propagates_effects() {
    let computation = cons(
        apply(
            lambda(Symbol(1), Computation::Var(Symbol(1))),
            Computation::Quote(Symbol(2)),
        ),
        error(ErrorName(3)),
    );

    assert_eq!(
        step(&computation),
        Step::Reduced(cons(Computation::Quote(Symbol(2)), error(ErrorName(3))))
    );
    assert_eq!(normal_form(&computation), error(ErrorName(3)));
}

#[test]
fn head_and_tail_destructure_cons() {
    let tail_list = cons(Computation::Quote(Symbol(2)), Computation::Nil);
    let computation = cons(Computation::Quote(Symbol(1)), tail_list.clone());

    assert_eq!(
        step(&head(computation.clone())),
        Step::Reduced(Computation::Quote(Symbol(1)))
    );
    assert_eq!(step(&tail(computation)), Step::Reduced(tail_list));
}

#[test]
fn head_and_tail_open_computations_are_neutral() {
    assert_eq!(step(&head(Computation::Var(Symbol(1)))), Step::Normal);
    assert_eq!(step(&tail(Computation::Var(Symbol(1)))), Step::Normal);
}

#[test]
fn head_and_tail_known_non_cons_reduce_to_error() {
    assert_eq!(
        step(&head(Computation::Nil)),
        Step::Reduced(error(RUNTIME_ERROR))
    );
    assert_eq!(
        step(&tail(Computation::Nil)),
        Step::Reduced(error(RUNTIME_ERROR))
    );
}

#[test]
fn list_case_reduces_nil_and_cons() {
    let cons_value = cons(Computation::Quote(Symbol(1)), Computation::Nil);
    let cons_case = head(Computation::Var(Symbol(9)));

    assert_eq!(
        step(&list_case(
            Computation::Nil,
            Computation::Quote(Symbol(0)),
            Symbol(9),
            cons_case.clone(),
        )),
        Step::Reduced(Computation::Quote(Symbol(0)))
    );
    assert_eq!(
        normal_form(&list_case(
            cons_value,
            Computation::Quote(Symbol(0)),
            Symbol(9),
            cons_case,
        )),
        Computation::Quote(Symbol(1))
    );
}

#[test]
fn list_case_open_computation_is_neutral_and_known_non_list_reduces_to_error() {
    assert_eq!(
        step(&list_case(
            Computation::Var(Symbol(1)),
            Computation::Quote(Symbol(0)),
            Symbol(9),
            Computation::Quote(Symbol(1)),
        )),
        Step::Normal
    );
    assert_eq!(
        step(&list_case(
            Computation::Quote(Symbol(1)),
            Computation::Quote(Symbol(0)),
            Symbol(9),
            Computation::Quote(Symbol(1))
        )),
        Step::Reduced(error(RUNTIME_ERROR))
    );
}

#[test]
fn if_reduces_true_false_and_condition_first() {
    let condition = apply(
        lambda(Symbol(1), Computation::Var(Symbol(1))),
        Computation::Quote(TRUE_SYMBOL),
    );
    let computation = if_computation(
        condition,
        Computation::Quote(Symbol(9)),
        Computation::Quote(Symbol(10)),
    );

    assert_eq!(
        step(&computation),
        Step::Reduced(if_computation(
            Computation::Quote(TRUE_SYMBOL),
            Computation::Quote(Symbol(9)),
            Computation::Quote(Symbol(10)),
        ))
    );
    assert_eq!(normal_form(&computation), Computation::Quote(Symbol(9)));
    assert_eq!(
        normal_form(&if_computation(
            Computation::Quote(FALSE_SYMBOL),
            Computation::Quote(Symbol(9)),
            Computation::Quote(Symbol(10)),
        )),
        Computation::Quote(Symbol(10))
    );
}

#[test]
fn if_does_not_evaluate_unchosen_branch() {
    assert_eq!(
        normal_form(&if_computation(
            Computation::Quote(TRUE_SYMBOL),
            Computation::Quote(Symbol(9)),
            Computation::Diverge,
        )),
        Computation::Quote(Symbol(9))
    );
    assert_eq!(
        normal_form(&if_computation(
            Computation::Quote(FALSE_SYMBOL),
            Computation::Diverge,
            Computation::Quote(Symbol(10)),
        )),
        Computation::Quote(Symbol(10))
    );
}

#[test]
fn if_open_condition_is_neutral_and_non_bool_values_error() {
    assert_eq!(
        step(&if_computation(
            Computation::Var(Symbol(1)),
            Computation::Quote(Symbol(9)),
            Computation::Quote(Symbol(10)),
        )),
        Step::Normal
    );
    assert_eq!(
        step(&if_computation(
            Computation::Quote(Symbol(11)),
            Computation::Quote(Symbol(9)),
            Computation::Quote(Symbol(10)),
        )),
        Step::Reduced(error(RUNTIME_ERROR))
    );
    assert_eq!(
        step(&if_computation(
            Computation::Nil,
            Computation::Quote(Symbol(9)),
            Computation::Quote(Symbol(10)),
        )),
        Step::Reduced(error(RUNTIME_ERROR))
    );
}

#[test]
fn if_propagates_condition_effects() {
    assert_eq!(
        normal_form(&if_computation(
            error(ErrorName(7)),
            Computation::Quote(Symbol(9)),
            Computation::Quote(Symbol(10)),
        )),
        error(ErrorName(7))
    );
    assert_eq!(
        normal_form(&if_computation(
            Computation::Diverge,
            Computation::Quote(Symbol(9)),
            Computation::Quote(Symbol(10)),
        )),
        Computation::Diverge
    );
}

#[test]
fn symbol_eq_reduces_after_evaluating_operands_left_to_right() {
    let left = apply(
        lambda(Symbol(1), Computation::Var(Symbol(1))),
        Computation::Quote(Symbol(9)),
    );
    let computation = symbol_eq_computation(left, Computation::Quote(Symbol(9)));

    assert_eq!(
        step(&computation),
        Step::Reduced(symbol_eq_computation(
            Computation::Quote(Symbol(9)),
            Computation::Quote(Symbol(9)),
        ))
    );
    assert_eq!(normal_form(&computation), Computation::Quote(TRUE_SYMBOL));
}

#[test]
fn symbol_eq_returns_false_for_distinct_or_non_symbol_values() {
    assert_eq!(
        normal_form(&symbol_eq_computation(
            Computation::Quote(Symbol(9)),
            Computation::Quote(Symbol(10)),
        )),
        Computation::Quote(FALSE_SYMBOL)
    );
    assert_eq!(
        normal_form(&symbol_eq_computation(
            Computation::Nil,
            Computation::Quote(Symbol(10)),
        )),
        Computation::Quote(FALSE_SYMBOL)
    );
    assert_eq!(
        normal_form(&symbol_eq_computation(
            Computation::Quote(Symbol(10)),
            lambda(Symbol(1), Computation::Var(Symbol(1))),
        )),
        Computation::Quote(FALSE_SYMBOL)
    );
}

#[test]
fn symbol_eq_open_operands_are_neutral_and_effects_propagate() {
    assert_eq!(
        step(&symbol_eq_computation(
            Computation::Var(Symbol(1)),
            Computation::Quote(Symbol(9)),
        )),
        Step::Normal
    );
    assert_eq!(
        normal_form(&symbol_eq_computation(
            error(ErrorName(7)),
            Computation::Quote(Symbol(9)),
        )),
        error(ErrorName(7))
    );
    assert_eq!(
        normal_form(&symbol_eq_computation(
            Computation::Quote(Symbol(9)),
            Computation::Diverge,
        )),
        Computation::Diverge
    );
}

#[test]
fn value_kind_reduces_after_evaluating_input() {
    let input = apply(
        lambda(Symbol(1), Computation::Var(Symbol(1))),
        Computation::Quote(Symbol(9)),
    );
    let computation = value_kind_computation(input);

    assert_eq!(
        step(&computation),
        Step::Reduced(value_kind_computation(Computation::Quote(Symbol(9))))
    );
    assert_eq!(
        normal_form(&computation),
        Computation::Quote(SYMBOL_KIND_SYMBOL)
    );
}

#[test]
fn value_kind_returns_symbol_lambda_or_list() {
    assert_eq!(
        normal_form(&value_kind_computation(Computation::Quote(Symbol(9)))),
        Computation::Quote(SYMBOL_KIND_SYMBOL)
    );
    assert_eq!(
        normal_form(&value_kind_computation(lambda(
            Symbol(1),
            Computation::Var(Symbol(1)),
        ))),
        Computation::Quote(LAMBDA_KIND_SYMBOL)
    );
    assert_eq!(
        normal_form(&value_kind_computation(Computation::Nil)),
        Computation::Quote(LIST_KIND_SYMBOL)
    );
    assert_eq!(
        normal_form(&value_kind_computation(cons(
            Computation::Quote(Symbol(9)),
            Computation::Nil,
        ))),
        Computation::Quote(LIST_KIND_SYMBOL)
    );
}

#[test]
fn value_kind_open_input_is_neutral_and_effects_propagate() {
    assert_eq!(
        step(&value_kind_computation(Computation::Var(Symbol(1)))),
        Step::Normal
    );
    assert_eq!(
        normal_form(&value_kind_computation(error(ErrorName(7)))),
        error(ErrorName(7))
    );
    assert_eq!(
        normal_form(&value_kind_computation(Computation::Diverge)),
        Computation::Diverge
    );
}

#[test]
fn value_kind_malformed_list_reduces_to_error() {
    assert_eq!(
        normal_form(&value_kind_computation(cons(
            Computation::Quote(Symbol(9)),
            Computation::Quote(Symbol(10)),
        ))),
        error(RUNTIME_ERROR)
    );
}

#[test]
fn step_proof_proves_if_reduction() {
    let computation = if_computation(
        Computation::Quote(TRUE_SYMBOL),
        Computation::Quote(Symbol(9)),
        Computation::Diverge,
    );

    assert!(check(
        &Proof::Step(computation.clone()),
        &equal(computation, Computation::Quote(Symbol(9))),
    ));
}

#[test]
fn step_proof_proves_symbol_eq_reduction() {
    let computation =
        symbol_eq_computation(Computation::Quote(Symbol(9)), Computation::Quote(Symbol(9)));

    assert!(check(
        &Proof::Step(computation.clone()),
        &equal(computation, Computation::Quote(TRUE_SYMBOL)),
    ));
}

#[test]
fn step_proof_proves_value_kind_reduction() {
    let computation = value_kind_computation(Computation::Quote(Symbol(9)));

    assert!(check(
        &Proof::Step(computation.clone()),
        &equal(computation, Computation::Quote(SYMBOL_KIND_SYMBOL)),
    ));
}

#[test]
fn step_proof_uses_context_to_prove_value_kind_list_reduction() {
    let computation = value_kind_computation(Computation::Var(Symbol(1)));
    let mut context = Context::new();
    context.insert(Symbol(99), is_list(Computation::Var(Symbol(1))));

    assert!(check_in_context(
        &Proof::Step(computation.clone()),
        &equal(computation, Computation::Quote(LIST_KIND_SYMBOL)),
        &context,
    ));
}

#[test]
fn substitution_descends_into_cons_and_destructors() {
    let computation = cons(
        head(Computation::Var(Symbol(1))),
        tail(Computation::Var(Symbol(2))),
    );

    assert_eq!(
        substitute(&computation, Symbol(1), &Computation::Quote(Symbol(3))),
        cons(
            head(Computation::Quote(Symbol(3))),
            tail(Computation::Var(Symbol(2)))
        )
    );
}

#[test]
fn substitution_and_free_symbols_descend_into_if() {
    let computation = if_computation(
        Computation::Var(Symbol(1)),
        Computation::Var(Symbol(2)),
        Computation::Quote(Symbol(3)),
    );

    assert_eq!(
        free_symbols(&computation),
        HashSet::from([Symbol(1), Symbol(2)])
    );
    assert_eq!(
        substitute(&computation, Symbol(1), &Computation::Quote(TRUE_SYMBOL)),
        if_computation(
            Computation::Quote(TRUE_SYMBOL),
            Computation::Var(Symbol(2)),
            Computation::Quote(Symbol(3)),
        )
    );
}

#[test]
fn substitution_and_free_symbols_descend_into_symbol_eq() {
    let computation =
        symbol_eq_computation(Computation::Var(Symbol(1)), Computation::Var(Symbol(2)));

    assert_eq!(
        free_symbols(&computation),
        HashSet::from([Symbol(1), Symbol(2)])
    );
    assert_eq!(
        substitute(&computation, Symbol(1), &Computation::Quote(Symbol(9))),
        symbol_eq_computation(Computation::Quote(Symbol(9)), Computation::Var(Symbol(2)))
    );
}

#[test]
fn substitution_and_free_symbols_descend_into_value_kind() {
    let computation = value_kind_computation(Computation::Var(Symbol(1)));

    assert_eq!(free_symbols(&computation), HashSet::from([Symbol(1)]));
    assert_eq!(
        substitute(&computation, Symbol(1), &Computation::Quote(Symbol(9))),
        value_kind_computation(Computation::Quote(Symbol(9)))
    );
}

#[test]
fn substitution_avoids_lambda_capture() {
    let computation = lambda(Symbol(2), Computation::Var(Symbol(1)));

    assert_eq!(
        substitute(&computation, Symbol(1), &Computation::Var(Symbol(2))),
        lambda(Symbol(0), Computation::Var(Symbol(2)))
    );
}

#[test]
fn substitution_avoids_list_case_capture() {
    let computation = list_case(
        Computation::Var(Symbol(1)),
        Computation::Quote(Symbol(0)),
        Symbol(2),
        Computation::Var(Symbol(3)),
    );

    assert_eq!(
        substitute(&computation, Symbol(3), &Computation::Var(Symbol(2))),
        list_case(
            Computation::Var(Symbol(1)),
            Computation::Quote(Symbol(0)),
            Symbol(4),
            Computation::Var(Symbol(2))
        )
    );
}

#[test]
fn free_symbols_ignore_list_case_cons_binder() {
    assert_eq!(
        free_symbols(&list_case(
            Computation::Var(Symbol(1)),
            Computation::Var(Symbol(2)),
            Symbol(3),
            apply(Computation::Var(Symbol(3)), Computation::Var(Symbol(4)))
        )),
        HashSet::from([Symbol(1), Symbol(2), Symbol(4)])
    );
}

#[test]
fn step_proof_proves_one_step_reduction() {
    let computation = head(cons(Computation::Quote(Symbol(1)), Computation::Nil));

    assert!(check(
        &Proof::Step(computation.clone()),
        &equal(computation, Computation::Quote(Symbol(1)))
    ));
}

#[test]
fn steps_proof_proves_multi_step_reduction() {
    let start = apply(
        lambda(Symbol(1), Computation::Quote(Symbol(9))),
        apply(
            lambda(Symbol(2), Computation::Var(Symbol(2))),
            Computation::Quote(Symbol(3)),
        ),
    );
    let middle = apply(
        lambda(Symbol(1), Computation::Quote(Symbol(9))),
        Computation::Quote(Symbol(3)),
    );
    let end = Computation::Quote(Symbol(9));

    assert!(check(
        &Proof::Steps(vec![start.clone(), middle, end.clone()]),
        &equal(start, end)
    ));
}

#[test]
fn theorem_from_proof_checks_closed_proofs() {
    let open_prop = equal(Computation::Var(Symbol(1)), Computation::Var(Symbol(1)));
    let valid = Theorem::from_proof(
        Proof::Refl(Computation::Quote(Symbol(1))),
        equal(Computation::Quote(Symbol(1)), Computation::Quote(Symbol(1))),
    );
    let invalid = Theorem::from_proof(
        Proof::Refl(Computation::Quote(Symbol(1))),
        equal(Computation::Quote(Symbol(1)), Computation::Quote(Symbol(2))),
    );

    assert!(valid.is_some());
    assert!(invalid.is_none());
    assert_eq!(
        Theorem::from_proof_result(
            Proof::Refl(Computation::Quote(Symbol(1))),
            equal(Computation::Quote(Symbol(1)), Computation::Quote(Symbol(2))),
        ),
        Err(TheoremError::InvalidProof)
    );
    assert!(check(&Proof::Refl(Computation::Var(Symbol(1))), &open_prop));
    assert!(
        Theorem::from_proof(Proof::Refl(Computation::Var(Symbol(1))), open_prop.clone()).is_none()
    );
    assert_eq!(
        Theorem::from_proof_result(Proof::Refl(Computation::Var(Symbol(1))), open_prop),
        Err(TheoremError::OpenProp(vec![Symbol(1)]))
    );
    assert!(Theorem::refl(Computation::Var(Symbol(1))).is_none());
    assert!(
        Theorem::from_proof(
            Proof::Assume(Symbol(7)),
            equal(Computation::Quote(Symbol(1)), Computation::Quote(Symbol(1)))
        )
        .is_none()
    );
}

#[test]
fn theory_known_proofs_cite_named_theorems() {
    let name = Name(42);
    let theorem = Theorem::refl(Computation::Quote(Symbol(1))).expect("closed refl should check");
    let replacement =
        Theorem::refl(Computation::Quote(Symbol(2))).expect("closed refl should check");
    let mut theory = Theory::new();

    assert!(theory.define_theorem(name, &theorem));
    assert!(!theory.define_theorem(name, &replacement));
    assert_eq!(theory.theorem(name), Some(theorem.prop()));
    assert!(theory.check(&Proof::Known(name), theorem.prop()));
    assert!(!check(&Proof::Known(name), theorem.prop()));

    let known = theory.known(name).expect("known theorem should check");
    assert_eq!(known.prop(), theorem.prop());
}

#[test]
fn theory_defines_closed_computations() {
    let name = Name(4);
    let computation = Computation::Quote(Symbol(1));
    let replacement = Computation::Quote(Symbol(2));
    let theorem = Theorem::refl(Computation::Nil).expect("closed refl should check");
    let mut theory = Theory::new();

    assert!(theory.define_computation(name, &computation));
    assert_eq!(theory.computation(name), Some(&computation));
    assert!(!theory.define_computation(name, &replacement));
    assert_eq!(
        theory.define_computation_result(name, &replacement),
        Err(ComputationDefinitionError::ComputationNameAlreadyDefined(
            name
        ))
    );
    assert!(!theory.define_theorem(name, &theorem));
    assert!(!theory.define_computation(Name(5), &Computation::Var(Symbol(1))));
    assert_eq!(
        theory.define_computation_result(Name(5), &Computation::Var(Symbol(1))),
        Err(ComputationDefinitionError::OpenComputation(vec![Symbol(1)]))
    );

    assert!(theory.define_theorem(Name(6), &theorem));
    assert!(!theory.define_computation(Name(6), &Computation::Nil));
    assert_eq!(
        theory.define_computation_result(Name(6), &Computation::Nil),
        Err(ComputationDefinitionError::TheoremNameAlreadyDefined(Name(
            6
        )))
    );
}

#[test]
fn computation_definitions_unfold_during_evaluation() {
    let id = Name(8);
    let id_computation = lambda(Symbol(1), Computation::Var(Symbol(1)));
    let argument = Computation::Quote(Symbol(2));
    let call = apply(Computation::Ref(id), argument.clone());
    let mut theory = Theory::new();

    assert_eq!(step(&Computation::Ref(id)), Step::Normal);
    assert_eq!(
        step(&apply(Computation::Ref(Name(9)), argument.clone())),
        Step::Normal
    );

    assert!(theory.define_computation(id, &id_computation));
    assert_eq!(
        theory.reduce(&Computation::Ref(id)),
        Step::Reduced(id_computation.clone())
    );
    assert_eq!(theory.normal_form(&call), argument.clone());
    assert_eq!(normal_form(&call), call);
}

#[test]
fn step_proofs_use_bindings_computation_definitions() {
    let name = Name(11);
    let computation = Computation::Ref(name);
    let value = Computation::Quote(Symbol(7));
    let mut theory = Theory::new();

    assert!(theory.define_computation(name, &value));
    assert!(theory.check(
        &Proof::Step(computation.clone()),
        &equal(computation.clone(), value.clone())
    ));
    assert!(!check(
        &Proof::Step(computation.clone()),
        &equal(computation.clone(), value.clone())
    ));

    let theorem = theory
        .step(computation.clone())
        .expect("defined constant should step");
    assert_eq!(theorem.prop(), &equal(computation, value));
}

#[test]
fn raw_checker_known_proofs_compose_with_rules() {
    let start = head(cons(Computation::Quote(Symbol(1)), Computation::Nil));
    let end = Computation::Quote(Symbol(1));
    let step = Theorem::step(start.clone()).expect("computation should step");
    let mut bindings = Bindings::new();

    assert!(bindings.define_theorem_result(Name(7), &step).is_ok());
    assert!(check_in_bindings(
        &Proof::Symm(Box::new(Proof::Known(Name(7)))),
        &equal(end, start),
        &bindings,
    ));
}

#[test]
fn theory_combinators_use_their_bindings() {
    let start = head(cons(Computation::Quote(Symbol(1)), Computation::Nil));
    let end = Computation::Quote(Symbol(1));
    let step = Theorem::step(start.clone()).expect("computation should step");
    let mut theory = Theory::new();

    assert!(theory.define_theorem(Name(7), &step));
    let known = theory.known(Name(7)).expect("known theorem should check");

    assert!(Theorem::symm(&known).is_none());
    assert_eq!(
        theory
            .symm(&known)
            .expect("known theorem should compose")
            .prop(),
        &equal(end, start)
    );
}

#[test]
fn theorem_equality_rules_build_checked_theorems() {
    let start = apply(
        lambda(Symbol(1), Computation::Var(Symbol(1))),
        Computation::Quote(Symbol(2)),
    );
    let step = Theorem::step(start.clone()).expect("computation should step");
    let refl = Theorem::refl(Computation::Quote(Symbol(2))).expect("closed refl should check");
    let trans = Theorem::trans(&step, &refl).expect("equalities should chain");
    let symm = Theorem::symm(&step).expect("step equality should be symmetric");

    assert_eq!(
        step.prop(),
        &equal(start.clone(), Computation::Quote(Symbol(2)))
    );
    assert_eq!(
        trans.prop(),
        &equal(start.clone(), Computation::Quote(Symbol(2)))
    );
    assert_eq!(symm.prop(), &equal(Computation::Quote(Symbol(2)), start));
    assert!(Theorem::step(Computation::Quote(Symbol(2))).is_none());
}

#[test]
fn theorem_rewrite_moves_props_across_equality() {
    let computation = apply(
        lambda(Symbol(1), Computation::Var(Symbol(1))),
        Computation::Nil,
    );
    let step = Theorem::step(computation.clone()).expect("computation should step");
    let nil_to_computation = Theorem::symm(&step).expect("step should be symmetric");
    let nil_refl = Theorem::refl(Computation::Nil).expect("closed refl should check");
    let template = equal(Computation::Var(Symbol(99)), Computation::Var(Symbol(99)));
    let theorem = Theorem::rewrite(&nil_to_computation, &nil_refl, Symbol(99), template)
        .expect("rewrite should move equality through a template");

    assert_eq!(theorem.prop(), &equal(computation.clone(), computation));
}

#[test]
fn theorem_first_order_rules_build_checked_theorems() {
    let prop = equal(Computation::Quote(Symbol(1)), Computation::Quote(Symbol(1)));
    let implication = Theorem::from_proof(
        Proof::ImpliesIntro {
            assumption: Symbol(7),
            premise: prop.clone(),
            proof: Box::new(Proof::Assume(Symbol(7))),
        },
        implies(prop.clone(), prop.clone()),
    )
    .expect("identity implication should check");
    let premise = Theorem::refl(Computation::Quote(Symbol(1))).expect("closed refl should check");
    let conclusion =
        Theorem::implies_elim(&implication, &premise).expect("modus ponens should apply");
    let universal = Theorem::from_proof(
        Proof::ForAllIntro {
            variable: Symbol(1),
            proof: Box::new(Proof::Refl(Computation::Var(Symbol(1)))),
        },
        forall(
            Symbol(1),
            equal(Computation::Var(Symbol(1)), Computation::Var(Symbol(1))),
        ),
    )
    .expect("forall intro should check");
    let instance = Theorem::forall_elim(&universal, Computation::Quote(Symbol(2)))
        .expect("forall theorem should instantiate");

    assert_eq!(conclusion.prop(), &prop);
    assert!(Theorem::forall_elim(&universal, Computation::Var(Symbol(2))).is_none());
    assert_eq!(
        instance.prop(),
        &equal(Computation::Quote(Symbol(2)), Computation::Quote(Symbol(2)))
    );
}

#[test]
fn theorem_exists_intro_supports_predicate_witnesses() {
    let variable = Symbol(1);
    let body = equal(Computation::Var(variable), Computation::Nil);
    let proof = Theorem::refl(Computation::Nil).expect("closed refl should check");
    let predicate = is_list(Computation::Var(variable));
    let theorem = Theorem::exists_intro_where(
        variable,
        predicate.clone(),
        body.clone(),
        Computation::Nil,
        &proof,
    )
    .expect("nil is a list witness");

    assert_eq!(
        theorem.prop(),
        &exists_where(variable, predicate.clone(), body)
    );
    assert!(
        Theorem::exists_intro_where(
            variable,
            predicate,
            equal(Computation::Var(variable), Computation::Quote(Symbol(2))),
            Computation::Quote(Symbol(2)),
            &Theorem::refl(Computation::Quote(Symbol(2))).expect("closed refl should check"),
        )
        .is_none()
    );
}

#[test]
fn rewrite_uses_equality_inside_template() {
    let start = head(cons(Computation::Quote(Symbol(1)), Computation::Nil));
    let end = Computation::Quote(Symbol(1));
    let template = equal(
        cons(Computation::Var(Symbol(99)), Computation::Nil),
        cons(Computation::Var(Symbol(99)), Computation::Nil),
    );
    let left_instance = substitute_prop(&template, Symbol(99), &start);
    let right_instance = substitute_prop(&template, Symbol(99), &end);
    let proof = Proof::Rewrite {
        equality: Box::new(Proof::Step(start)),
        proof: Box::new(Proof::Refl(match left_instance.clone() {
            Prop::Equal(left, _) => left,
            _ => unreachable!(),
        })),
        variable: Symbol(99),
        template,
    };

    assert!(check(&proof, &right_instance));
}

#[test]
fn step_proof_reduces_arguments_before_beta() {
    let lam = Lambda {
        parameter: Symbol(1),
        body: Box::new(Computation::Quote(Symbol(9))),
    };
    let argument = apply(
        lambda(Symbol(2), Computation::Var(Symbol(2))),
        Computation::Quote(Symbol(3)),
    );

    assert!(!check(
        &Proof::Step(apply(Computation::Lambda(lam.clone()), argument.clone())),
        &Prop::Equal(
            apply(Computation::Lambda(lam), argument),
            Computation::Quote(Symbol(9))
        )
    ));
}

#[test]
fn beta_reduction_requires_value_premise() {
    let variable = Symbol(1);
    let lambda_value = Lambda {
        parameter: Symbol(2),
        body: Box::new(Computation::Var(Symbol(2))),
    };
    let application = apply(
        Computation::Lambda(lambda_value.clone()),
        Computation::Var(variable),
    );
    let proof = Proof::ForAllIntro {
        variable,
        proof: Box::new(Proof::ImpliesIntro {
            assumption: variable,
            premise: is_value(Computation::Var(variable)),
            proof: Box::new(Proof::Step(application.clone())),
        }),
    };
    let expected = forall_where(
        variable,
        is_value(Computation::Var(variable)),
        equal(application, Computation::Var(variable)),
    );
    let missing_premise_proof = Proof::ForAllIntro {
        variable,
        proof: Box::new(Proof::Step(apply(
            Computation::Lambda(lambda_value),
            Computation::Var(variable),
        ))),
    };

    assert!(check(&proof, &expected));
    assert!(!check(
        &missing_premise_proof,
        &forall(
            variable,
            equal(
                apply(
                    lambda(Symbol(2), Computation::Var(Symbol(2))),
                    Computation::Var(variable),
                ),
                Computation::Var(variable),
            ),
        )
    ));
}

#[test]
fn list_reductions_require_value_and_list_premises() {
    let head_symbol = Symbol(1);
    let tail_symbol = Symbol(2);
    let list = cons(Computation::Var(head_symbol), Computation::Var(tail_symbol));
    let cons_case = head(Computation::Var(Symbol(9)));
    let destructure = list_case(
        list.clone(),
        Computation::Quote(Symbol(0)),
        Symbol(9),
        cons_case,
    );
    let destructured_head = head(list.clone());
    let proof = Proof::ForAllIntro {
        variable: head_symbol,
        proof: Box::new(Proof::ImpliesIntro {
            assumption: head_symbol,
            premise: is_value(Computation::Var(head_symbol)),
            proof: Box::new(Proof::ForAllIntro {
                variable: tail_symbol,
                proof: Box::new(Proof::ImpliesIntro {
                    assumption: tail_symbol,
                    premise: is_list(Computation::Var(tail_symbol)),
                    proof: Box::new(Proof::Steps(vec![
                        destructure.clone(),
                        destructured_head,
                        Computation::Var(head_symbol),
                    ])),
                }),
            }),
        }),
    };
    let expected = forall_where(
        head_symbol,
        is_value(Computation::Var(head_symbol)),
        forall_where(
            tail_symbol,
            is_list(Computation::Var(tail_symbol)),
            equal(destructure, Computation::Var(head_symbol)),
        ),
    );
    let missing_tail_premise_proof = Proof::ForAllIntro {
        variable: head_symbol,
        proof: Box::new(Proof::ImpliesIntro {
            assumption: head_symbol,
            premise: is_value(Computation::Var(head_symbol)),
            proof: Box::new(Proof::ForAllIntro {
                variable: tail_symbol,
                proof: Box::new(Proof::Step(list_case(
                    list,
                    Computation::Quote(Symbol(0)),
                    Symbol(9),
                    head(Computation::Var(Symbol(9))),
                ))),
            }),
        }),
    };

    assert!(check(&proof, &expected));
    assert!(!check(
        &missing_tail_premise_proof,
        &forall_where(
            head_symbol,
            is_value(Computation::Var(head_symbol)),
            forall(
                tail_symbol,
                equal(
                    list_case(
                        cons(Computation::Var(head_symbol), Computation::Var(tail_symbol),),
                        Computation::Quote(Symbol(0)),
                        Symbol(9),
                        head(Computation::Var(Symbol(9))),
                    ),
                    Computation::Var(head_symbol),
                ),
            ),
        )
    ));
}

#[test]
fn list_induction_proves_reflexivity_for_lists() {
    let variable = Symbol(1);
    let head = Symbol(2);
    let tail = Symbol(3);
    let induction_hypothesis_assumption = Symbol(6);
    let property = equal(Computation::Var(variable), Computation::Var(variable));
    let proof = Proof::ListInduction {
        variable,
        property: property.clone(),
        base: Box::new(Proof::Refl(Computation::Nil)),
        head,
        tail,
        induction_hypothesis_assumption,
        step: Box::new(Proof::Refl(cons(
            Computation::Var(head),
            Computation::Var(tail),
        ))),
    };
    let expected = forall_where(variable, is_list(Computation::Var(variable)), property);

    assert!(check(&proof, &expected));
}

#[test]
fn list_induction_rejects_stale_step_variables() {
    let variable = Symbol(1);
    let head = variable;
    let tail = Symbol(3);
    let induction_hypothesis_assumption = Symbol(6);
    let property = equal(Computation::Var(variable), Computation::Var(variable));
    let proof = Proof::ListInduction {
        variable,
        property: property.clone(),
        base: Box::new(Proof::Refl(Computation::Nil)),
        head,
        tail,
        induction_hypothesis_assumption,
        step: Box::new(Proof::Assume(induction_hypothesis_assumption)),
    };
    let expected = forall_where(variable, is_list(Computation::Var(variable)), property);

    assert!(!check(&proof, &expected));
}

#[test]
fn assume_uses_context() {
    let prop = equal(Computation::Quote(Symbol(1)), Computation::Quote(Symbol(1)));
    let mut context = Context::new();
    context.insert(Symbol(7), prop.clone());

    assert!(check_in_context(&Proof::Assume(Symbol(7)), &prop, &context));
    assert!(!check(&Proof::Assume(Symbol(7)), &prop));
}

#[test]
fn implies_intro_and_elim_work() {
    let prop = equal(Computation::Quote(Symbol(1)), Computation::Quote(Symbol(1)));
    let proof = Proof::ImpliesElim {
        implication: Box::new(Proof::ImpliesIntro {
            assumption: Symbol(7),
            premise: prop.clone(),
            proof: Box::new(Proof::Assume(Symbol(7))),
        }),
        premise: Box::new(Proof::Refl(Computation::Quote(Symbol(1)))),
    };

    assert!(check(&proof, &prop));
}

#[test]
fn forall_intro_and_elim_work() {
    let proof = Proof::ForAllElim {
        forall: Box::new(Proof::ForAllIntro {
            variable: Symbol(1),
            proof: Box::new(Proof::Refl(Computation::Var(Symbol(1)))),
        }),
        argument: Computation::Quote(Symbol(2)),
    };

    assert!(check(
        &proof,
        &equal(Computation::Quote(Symbol(2)), Computation::Quote(Symbol(2)))
    ));
}

#[test]
fn exists_intro_and_elim_work() {
    let body = equal(Computation::Var(Symbol(1)), Computation::Var(Symbol(1)));
    let conclusion = equal(Computation::Quote(Symbol(0)), Computation::Quote(Symbol(0)));
    let proof = Proof::ExistsElim {
        existential: Box::new(Proof::ExistsIntro {
            variable: Symbol(1),
            body,
            witness: Computation::Quote(Symbol(2)),
            proof: Box::new(Proof::Refl(Computation::Quote(Symbol(2)))),
        }),
        witness: Symbol(9),
        assumption: Symbol(7),
        proof: Box::new(Proof::Refl(Computation::Quote(Symbol(0)))),
    };

    assert!(check(&proof, &conclusion));
}

#[test]
fn and_or_rules_work() {
    let left = equal(Computation::Quote(Symbol(1)), Computation::Quote(Symbol(1)));
    let right = equal(Computation::Quote(Symbol(2)), Computation::Quote(Symbol(2)));
    let and_proof = Proof::AndIntro(
        Box::new(Proof::Refl(Computation::Quote(Symbol(1)))),
        Box::new(Proof::Refl(Computation::Quote(Symbol(2)))),
    );

    assert!(check(
        &Proof::AndElimLeft(Box::new(and_proof.clone())),
        &left
    ));
    assert!(check(&Proof::AndElimRight(Box::new(and_proof)), &right));

    let or_proof = Proof::OrElim {
        disjunction: Box::new(Proof::OrIntroLeft {
            proof: Box::new(Proof::Refl(Computation::Quote(Symbol(1)))),
            right: left.clone(),
        }),
        left_assumption: Symbol(7),
        left_proof: Box::new(Proof::Assume(Symbol(7))),
        right_assumption: Symbol(8),
        right_proof: Box::new(Proof::Assume(Symbol(8))),
    };

    assert!(check(&or_proof, &left));
}

#[test]
fn substitute_prop_avoids_quantifier_capture() {
    let prop = forall(
        Symbol(2),
        equal(Computation::Var(Symbol(1)), Computation::Var(Symbol(2))),
    );

    assert_eq!(
        substitute_prop(&prop, Symbol(1), &Computation::Var(Symbol(2))),
        forall(
            Symbol(0),
            equal(Computation::Var(Symbol(2)), Computation::Var(Symbol(0)))
        )
    );
}

#[test]
fn exists_intro_uses_witness() {
    let body = equal(Computation::Var(Symbol(1)), Computation::Var(Symbol(1)));
    let proof = Proof::ExistsIntro {
        variable: Symbol(1),
        body: body.clone(),
        witness: Computation::Quote(Symbol(2)),
        proof: Box::new(Proof::Refl(Computation::Quote(Symbol(2)))),
    };

    assert!(check(&proof, &exists(Symbol(1), body)));
}

#[test]
fn primitive_proof_proves_structural_props() {
    let prop = is_list(Computation::Nil);

    assert!(check(&Proof::Primitive(prop.clone()), &prop));
    assert!(!check(
        &Proof::Primitive(is_list(Computation::Quote(Symbol(1)))),
        &is_list(Computation::Quote(Symbol(1)))
    ));
}

#[test]
fn symbol_eq_true_elim_inverts_true_symbol_comparisons() {
    let left = Computation::Quote(Symbol(8));
    let right = Computation::Quote(Symbol(8));
    let comparison = symbol_eq_computation(left.clone(), right.clone());
    let proof = Proof::SymbolEqTrueElim(Box::new(Proof::Step(comparison)));

    assert!(check(&proof, &equal(left, right)));

    let distinct_left = Computation::Quote(Symbol(8));
    let distinct_right = Computation::Quote(Symbol(9));
    let distinct = symbol_eq_computation(distinct_left.clone(), distinct_right.clone());
    let invalid = Proof::SymbolEqTrueElim(Box::new(Proof::Step(distinct)));

    assert!(!check(&invalid, &equal(distinct_left, distinct_right)));
}

#[test]
fn symbol_eq_reduces_reflexive_open_symbol_in_context() {
    let value = Computation::Var(Symbol(1));
    let comparison = symbol_eq_computation(value.clone(), value.clone());
    let expected = equal(comparison.clone(), Computation::Quote(TRUE_SYMBOL));
    assert!(!check(&Proof::Step(comparison.clone()), &expected));

    let mut context = Context::new();
    context.insert(Symbol(9), is_value(value.clone()));
    context.insert(
        Symbol(10),
        equal(
            symbol_eq_computation(
                value_kind_computation(value.clone()),
                Computation::Quote(SYMBOL_KIND_SYMBOL),
            ),
            Computation::Quote(TRUE_SYMBOL),
        ),
    );

    assert!(check_in_context(
        &Proof::Step(comparison),
        &expected,
        &context,
    ));
}

#[test]
fn if_true_with_false_else_elims_invert_boolean_results() {
    let condition = Computation::Quote(TRUE_SYMBOL);
    let then_branch = Computation::Quote(TRUE_SYMBOL);
    let else_branch = Computation::Quote(FALSE_SYMBOL);
    let conditional = if_computation(condition.clone(), then_branch.clone(), else_branch.clone());

    assert!(check(
        &Proof::IfTrueWithFalseElseCondition(Box::new(Proof::Step(conditional.clone()))),
        &equal(condition, Computation::Quote(TRUE_SYMBOL))
    ));
    assert!(check(
        &Proof::IfTrueWithFalseElseThen(Box::new(Proof::Step(conditional))),
        &equal(then_branch, Computation::Quote(TRUE_SYMBOL))
    ));

    let wrong_else = if_computation(
        Computation::Quote(TRUE_SYMBOL),
        Computation::Quote(TRUE_SYMBOL),
        Computation::Nil,
    );

    assert!(!check(
        &Proof::IfTrueWithFalseElseCondition(Box::new(Proof::Step(wrong_else))),
        &equal(
            Computation::Quote(TRUE_SYMBOL),
            Computation::Quote(TRUE_SYMBOL)
        )
    ));
}

#[test]
fn if_value_with_effect_then_elims_invert_effect_guards() {
    let condition = Computation::Quote(FALSE_SYMBOL);
    let then_branch = error(ErrorName(7));
    let else_branch = Computation::Quote(Symbol(8));
    let conditional = if_computation(condition.clone(), then_branch, else_branch.clone());

    assert!(check(
        &Proof::IfValueWithEffectThenConditionFalse(Box::new(Proof::Step(conditional.clone()))),
        &equal(condition, Computation::Quote(FALSE_SYMBOL))
    ));
    assert!(check(
        &Proof::IfValueWithEffectThenElse(Box::new(Proof::Step(conditional))),
        &equal(else_branch.clone(), else_branch)
    ));

    let not_effect_then = if_computation(
        Computation::Quote(TRUE_SYMBOL),
        Computation::Quote(TRUE_SYMBOL),
        Computation::Nil,
    );
    assert!(!check(
        &Proof::IfValueWithEffectThenConditionFalse(Box::new(Proof::Step(not_effect_then))),
        &equal(
            Computation::Quote(TRUE_SYMBOL),
            Computation::Quote(FALSE_SYMBOL)
        )
    ));

    let effect_result = if_computation(
        Computation::Quote(FALSE_SYMBOL),
        error(ErrorName(7)),
        Computation::Diverge,
    );
    assert!(!check(
        &Proof::IfValueWithEffectThenElse(Box::new(Proof::Step(effect_result))),
        &equal(Computation::Diverge, Computation::Diverge)
    ));
}

#[test]
fn if_value_condition_bool_extracts_boolean_condition() {
    let condition = Computation::Quote(TRUE_SYMBOL);
    let conditional = if_computation(condition.clone(), Computation::Nil, error(ErrorName(7)));

    assert!(check(
        &Proof::IfValueConditionBool(Box::new(Proof::Step(conditional))),
        &is_bool(condition)
    ));

    let effect_result = if_computation(
        Computation::Quote(FALSE_SYMBOL),
        Computation::Nil,
        error(ErrorName(7)),
    );
    assert!(!check(
        &Proof::IfValueConditionBool(Box::new(Proof::Step(effect_result))),
        &is_bool(Computation::Quote(FALSE_SYMBOL))
    ));
}

#[test]
fn if_value_condition_bool_uses_contextual_value_facts() {
    let condition = Computation::Quote(TRUE_SYMBOL);
    let result = Computation::Var(Symbol(99));
    let conditional = if_computation(condition.clone(), Computation::Nil, error(ErrorName(7)));
    let mut context = Context::new();
    context.insert(Symbol(99), is_value(result.clone()));
    context.insert(Symbol(100), equal(conditional, result));

    assert!(check_in_context(
        &Proof::IfValueConditionBool(Box::new(Proof::Assume(Symbol(100)))),
        &is_bool(condition),
        &context,
    ));
}

#[test]
fn apply_value_argument_extracts_argument_termination() {
    let witness = Symbol(99);
    let argument = apply(
        lambda(Symbol(1), Computation::Var(Symbol(1))),
        Computation::Quote(Symbol(7)),
    );
    let application = apply(
        lambda(Symbol(2), Computation::Quote(Symbol(8))),
        argument.clone(),
    );

    assert!(check(
        &Proof::ApplyValueArgument {
            variable: witness,
            proof: Box::new(Proof::Steps(vec![
                application.clone(),
                apply(
                    lambda(Symbol(2), Computation::Quote(Symbol(8))),
                    Computation::Quote(Symbol(7)),
                ),
                Computation::Quote(Symbol(8)),
            ])),
        },
        &terminates(witness, argument)
    ));

    let result = Computation::Var(Symbol(100));
    let mut context = Context::new();
    context.insert(Symbol(100), is_value(result.clone()));
    context.insert(Symbol(101), equal(application, result));
    assert!(check_in_context(
        &Proof::ApplyValueArgument {
            variable: witness,
            proof: Box::new(Proof::Assume(Symbol(101))),
        },
        &terminates(
            witness,
            apply(
                lambda(Symbol(1), Computation::Var(Symbol(1))),
                Computation::Quote(Symbol(7)),
            )
        ),
        &context,
    ));

    let non_value_result = apply(
        lambda(Symbol(2), Computation::Quote(Symbol(8))),
        Computation::Quote(Symbol(7)),
    );
    assert!(!check(
        &Proof::ApplyValueArgument {
            variable: witness,
            proof: Box::new(Proof::Refl(non_value_result)),
        },
        &terminates(witness, Computation::Quote(Symbol(7)))
    ));
}

#[test]
fn distinct_outcomes_prove_absurd_and_absurd_eliminates() {
    let assumption = Symbol(99);
    let contradiction = equal(
        Computation::Quote(TRUE_SYMBOL),
        Computation::Quote(FALSE_SYMBOL),
    );
    let target = is_value(Computation::Nil);
    let mut context = Context::new();
    context.insert(assumption, contradiction);

    let absurd_proof = Proof::DistinctOutcomes(Box::new(Proof::Assume(assumption)));
    assert!(check_in_context(&absurd_proof, &absurd(), &context));
    assert!(check_in_context(
        &Proof::AbsurdElim {
            absurd: Box::new(absurd_proof),
            prop: target.clone(),
        },
        &target,
        &context
    ));

    let matching_outcomes = Proof::DistinctOutcomes(Box::new(Proof::Refl(Computation::Nil)));
    assert!(!check(&matching_outcomes, &absurd()));
}

#[test]
fn distinct_outcomes_uses_contextual_value_constructors() {
    let tail_var = Computation::Var(Symbol(1));
    let cons_value = cons(Computation::Quote(Symbol(2)), tail_var.clone());
    let contradiction = equal(cons_value, Computation::Quote(Symbol(3)));
    let mut context = Context::new();
    context.insert(Symbol(1), is_list(tail_var));
    context.insert(Symbol(4), contradiction);

    assert!(check_in_context(
        &Proof::DistinctOutcomes(Box::new(Proof::Assume(Symbol(4)))),
        &absurd(),
        &context,
    ));
}

#[test]
fn non_symbol_non_lambda_values_are_lists() {
    let value = Computation::Var(Symbol(1));
    let value_assumption = Symbol(10);
    let not_symbol_assumption = Symbol(11);
    let not_lambda_assumption = Symbol(12);
    let mut context = Context::new();
    context.insert(value_assumption, is_value(value.clone()));
    context.insert(
        not_symbol_assumption,
        equal(
            symbol_eq_computation(
                value_kind_computation(value.clone()),
                Computation::Quote(SYMBOL_KIND_SYMBOL),
            ),
            Computation::Quote(FALSE_SYMBOL),
        ),
    );
    context.insert(
        not_lambda_assumption,
        equal(
            symbol_eq_computation(
                value_kind_computation(value.clone()),
                Computation::Quote(LAMBDA_KIND_SYMBOL),
            ),
            Computation::Quote(FALSE_SYMBOL),
        ),
    );

    let proof = Proof::ValueNonSymbolNonLambdaIsList {
        value: Box::new(Proof::Assume(value_assumption)),
        not_symbol: Box::new(Proof::Assume(not_symbol_assumption)),
        not_lambda: Box::new(Proof::Assume(not_lambda_assumption)),
    };

    assert!(check_in_context(&proof, &is_list(value.clone()), &context));

    let wrong_not_lambda = Proof::ValueNonSymbolNonLambdaIsList {
        value: Box::new(Proof::Assume(value_assumption)),
        not_symbol: Box::new(Proof::Assume(not_symbol_assumption)),
        not_lambda: Box::new(Proof::Assume(not_symbol_assumption)),
    };
    assert!(!check_in_context(
        &wrong_not_lambda,
        &is_list(value),
        &context
    ));
}

#[test]
fn value_induction_proves_values_are_values() {
    let value = Symbol(1);
    let symbol_assumption = Symbol(2);
    let lambda_assumption = Symbol(3);
    let head = Symbol(4);
    let tail = Symbol(5);
    let head_ih = Symbol(6);
    let tail_ih = Symbol(7);
    let property = is_value(Computation::Var(value));
    let cons_value = cons(Computation::Var(head), Computation::Var(tail));

    let proof = Proof::ValueInduction {
        variable: value,
        property: property.clone(),
        symbol_assumption,
        symbol_case: Box::new(Proof::Assume(value)),
        lambda_assumption,
        lambda_case: Box::new(Proof::Assume(value)),
        nil_case: Box::new(Proof::Primitive(is_value(Computation::Nil))),
        head,
        tail,
        head_induction_hypothesis_assumption: head_ih,
        tail_induction_hypothesis_assumption: tail_ih,
        cons_case: Box::new(Proof::Primitive(is_value(cons_value))),
    };
    let expected = forall_where(value, is_value(Computation::Var(value)), property.clone());

    assert!(check(&proof, &expected));

    let duplicate_symbol = Proof::ValueInduction {
        variable: value,
        property,
        symbol_assumption: value,
        symbol_case: Box::new(Proof::Assume(value)),
        lambda_assumption,
        lambda_case: Box::new(Proof::Assume(value)),
        nil_case: Box::new(Proof::Primitive(is_value(Computation::Nil))),
        head,
        tail,
        head_induction_hypothesis_assumption: head_ih,
        tail_induction_hypothesis_assumption: tail_ih,
        cons_case: Box::new(Proof::Primitive(is_value(cons(
            Computation::Var(head),
            Computation::Var(tail),
        )))),
    };
    assert!(!check(&duplicate_symbol, &expected));
}

#[test]
fn prop_helpers_construct_expected_shapes() {
    let prop = equal(Computation::Quote(Symbol(1)), Computation::Quote(Symbol(1)));
    let computation = apply(
        lambda(Symbol(1), Computation::Var(Symbol(1))),
        Computation::Quote(Symbol(2)),
    );

    assert_eq!(
        implies(prop.clone(), prop.clone()),
        Prop::Implies(Box::new(prop.clone()), Box::new(prop.clone()))
    );
    assert_eq!(
        forall_where(Symbol(8), prop.clone(), prop.clone()),
        forall(Symbol(8), implies(prop.clone(), prop.clone()))
    );
    assert_eq!(
        exists_where(Symbol(8), prop.clone(), prop.clone()),
        exists(Symbol(8), and(prop.clone(), prop.clone()))
    );
    assert_eq!(
        terminates(Symbol(9), computation.clone()),
        exists_value(
            Symbol(9),
            computes_to(computation.clone(), Computation::Var(Symbol(9))),
        )
    );
    assert_eq!(
        computes_to_list(Symbol(9), computation.clone()),
        exists_where(
            Symbol(9),
            is_list(Computation::Var(Symbol(9))),
            computes_to(computation.clone(), Computation::Var(Symbol(9))),
        )
    );
    assert_eq!(
        errors_with(computation.clone(), ErrorName(9)),
        computes_to_effect(computation.clone(), Effect::error(ErrorName(9)))
    );
    assert_eq!(
        diverges(computation.clone()),
        computes_to_effect(computation, Effect::diverge())
    );
    assert_eq!(
        or(prop.clone(), prop.clone()),
        Prop::Or(Box::new(prop.clone()), Box::new(prop))
    );
}
