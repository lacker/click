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

fn error(error: ErrorName) -> Computation {
    Computation::Error(error)
}

fn value_lambda(lambda: Lambda) -> Proof {
    Proof::Value(Value::lambda(lambda))
}

fn value_quote(symbol: Symbol) -> Proof {
    Proof::Value(Value::quote(symbol))
}

fn value_nil() -> Proof {
    Proof::Value(Value::nil())
}

#[test]
fn computations_classify_values_effects_and_outcomes() {
    let value_computation = cons(Computation::Quote(Symbol(1)), Computation::Nil);
    let value = Value::cons(Value::quote(Symbol(1)), Value::nil());
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
        sort: Sort::Computation,
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
    let theorem = Theorem::refl(Computation::Quote(Symbol(1)));
    let replacement = Theorem::refl(Computation::Quote(Symbol(2)));
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
    let theorem = Theorem::refl(Computation::Nil);
    let mut theory = Theory::new();

    assert!(theory.define_computation(name, &computation));
    assert_eq!(theory.computation(name), Some(&computation));
    assert!(!theory.define_computation(name, &replacement));
    assert!(!theory.define_theorem(name, &theorem));
    assert!(!theory.define_computation(Name(5), &Computation::Var(Symbol(1))));

    assert!(theory.define_theorem(Name(6), &theorem));
    assert!(!theory.define_computation(Name(6), &Computation::Nil));
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

    assert!(bindings.define_theorem(Name(7), &step));
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
    let refl = Theorem::refl(Computation::Quote(Symbol(2)));
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
    let theorem = Theorem::rewrite(
        &nil_to_computation,
        &Theorem::value_nil(),
        Symbol(99),
        is_value(Computation::Var(Symbol(99))),
    )
    .expect("rewrite should prove valuehood before evaluation");

    assert_eq!(theorem.prop(), &is_value(computation));
}

#[test]
fn theorem_value_rules_build_checked_theorems() {
    let head = Computation::Quote(Symbol(1));
    let tail = Computation::Nil;
    let head_value = Theorem::value_quote(Symbol(1));
    let list = cons(head.clone(), tail.clone());
    let value = Theorem::cons_is_value(head, tail, &head_value)
        .expect("cons with value head and list tail is a value");

    assert_eq!(value.prop(), &is_value(list));
    assert!(
        Theorem::cons_is_value(
            Computation::Quote(Symbol(1)),
            Computation::Quote(Symbol(2)),
            &head_value
        )
        .is_none()
    );
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
    let conclusion =
        Theorem::implies_elim(&implication, &Theorem::refl(Computation::Quote(Symbol(1))))
            .expect("modus ponens should apply");
    let universal = Theorem::from_proof(
        Proof::ForAllIntro {
            variable: Symbol(1),
            sort: Sort::Computation,
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
    assert_eq!(
        instance.prop(),
        &equal(Computation::Quote(Symbol(2)), Computation::Quote(Symbol(2)))
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
fn beta_proof_rejects_reducible_arguments() {
    let lam = Lambda {
        parameter: Symbol(1),
        body: Box::new(Computation::Quote(Symbol(9))),
    };
    let argument = apply(
        lambda(Symbol(2), Computation::Var(Symbol(2))),
        Computation::Quote(Symbol(3)),
    );

    assert!(!check(
        &Proof::Beta {
            lambda: lam.clone(),
            argument: argument.clone()
        },
        &Prop::Equal(
            apply(Computation::Lambda(lam), argument),
            Computation::Quote(Symbol(9))
        )
    ));
}

#[test]
fn value_intro_rules_prove_concrete_values() {
    let lambda = Lambda {
        parameter: Symbol(1),
        body: Box::new(Computation::Var(Symbol(1))),
    };
    let list_value = Value::cons(Value::quote(Symbol(1)), Value::nil());
    let list = list_value.clone().into_computation();
    let proof = Proof::ConsIsValue {
        head: Computation::Quote(Symbol(1)),
        tail: Computation::Nil,
        head_is_value: Box::new(value_quote(Symbol(1))),
    };

    assert!(check(
        &value_lambda(lambda.clone()),
        &is_value(Computation::Lambda(lambda))
    ));
    assert!(check(
        &value_quote(Symbol(1)),
        &is_value(Computation::Quote(Symbol(1)))
    ));
    assert!(check(&value_nil(), &is_value(Computation::Nil)));
    assert!(check(&Proof::Value(list_value), &is_value(list.clone())));
    assert!(check(&proof, &is_value(list)));
}

#[test]
fn cons_is_value_requires_matching_value_proofs() {
    let proof = Proof::ConsIsValue {
        head: Computation::Diverge,
        tail: Computation::Nil,
        head_is_value: Box::new(value_quote(Symbol(1))),
    };

    assert!(!check(
        &proof,
        &is_value(cons(Computation::Diverge, Computation::Nil))
    ));
}

#[test]
fn list_induction_proves_every_list_is_a_value() {
    let variable = Symbol(1);
    let head = Symbol(2);
    let tail = Symbol(3);
    let head_is_value_assumption = Symbol(4);
    let induction_hypothesis_assumption = Symbol(6);
    let property = is_value(Computation::Var(variable));
    let proof = Proof::ListInduction {
        variable,
        property: property.clone(),
        base: Box::new(value_nil()),
        head,
        tail,
        head_is_value_assumption,
        induction_hypothesis_assumption,
        step: Box::new(Proof::ConsIsValue {
            head: Computation::Var(head),
            tail: Computation::Var(tail),
            head_is_value: Box::new(Proof::Assume(head_is_value_assumption)),
        }),
    };
    let expected = forall_list(variable, is_value(Computation::Var(variable)));

    assert!(check(&proof, &expected));
}

#[test]
fn list_induction_rejects_stale_step_variables() {
    let variable = Symbol(1);
    let head = variable;
    let tail = Symbol(3);
    let head_is_value_assumption = Symbol(4);
    let induction_hypothesis_assumption = Symbol(6);
    let property = is_value(Computation::Var(variable));
    let proof = Proof::ListInduction {
        variable,
        property: property.clone(),
        base: Box::new(value_nil()),
        head,
        tail,
        head_is_value_assumption,
        induction_hypothesis_assumption,
        step: Box::new(Proof::Assume(head_is_value_assumption)),
    };
    let expected = forall_list(variable, property);

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
            sort: Sort::Computation,
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
            sort: Sort::Computation,
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
        sort: Sort::Computation,
        body: body.clone(),
        witness: Computation::Quote(Symbol(2)),
        proof: Box::new(Proof::Refl(Computation::Quote(Symbol(2)))),
    };

    assert!(check(&proof, &exists(Symbol(1), body)));
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
        Prop::Implies(Box::new(prop.clone()), Box::new(prop))
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
        exists_list(
            Symbol(9),
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
        or(
            is_value(Computation::Quote(Symbol(1))),
            is_value(Computation::Nil)
        ),
        Prop::Or(
            Box::new(Prop::IsValue(Computation::Quote(Symbol(1)))),
            Box::new(Prop::IsValue(Computation::Nil))
        )
    );
}
