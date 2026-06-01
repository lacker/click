use super::*;
use std::collections::HashSet;

fn lambda(parameter: Symbol, body: Term) -> Term {
    Term::Lambda(Lambda {
        parameter,
        body: Box::new(body),
    })
}

fn apply(function: Term, argument: Term) -> Term {
    Term::Apply {
        function: Box::new(function),
        argument: Box::new(argument),
    }
}

fn cons(head: Term, tail: Term) -> Term {
    Term::Cons {
        head: Box::new(head),
        tail: Box::new(tail),
    }
}

fn head(term: Term) -> Term {
    Term::Head(Box::new(term))
}

fn tail(term: Term) -> Term {
    Term::Tail(Box::new(term))
}

fn list_case(list: Term, nil: Term, cons_var: Symbol, cons_case: Term) -> Term {
    Term::ListCase(ListCase {
        list: Box::new(list),
        nil: Box::new(nil),
        cons: cons_var,
        cons_case: Box::new(cons_case),
    })
}

fn error(error: Term) -> Term {
    Term::Error(Box::new(error))
}

#[test]
fn computations_classify_values_effects_and_outcomes() {
    let value_computation = cons(Term::Quote(Symbol(1)), Term::Nil);
    let error_computation = error(Term::Quote(Symbol(2)));
    let pending_computation = apply(lambda(Symbol(1), Term::Var(Symbol(1))), Term::Nil);

    assert_eq!(
        value_computation.as_value().map(Value::into_computation),
        Some(value_computation)
    );
    assert_eq!(
        error_computation.as_effect(),
        Some(Effect::Error(Box::new(Term::Quote(Symbol(2)))))
    );
    assert_eq!(
        Term::Diverge.as_outcome(),
        Some(Outcome::Effect(Effect::Diverge))
    );
    assert_eq!(pending_computation.as_outcome(), None);
}

#[test]
fn alpha_eq_prop_renames_bound_variables_only() {
    let left = forall(
        Symbol(1),
        exists(Symbol(2), equal(Term::Var(Symbol(1)), Term::Var(Symbol(2)))),
    );
    let right = forall(
        Symbol(10),
        exists(
            Symbol(11),
            equal(Term::Var(Symbol(10)), Term::Var(Symbol(11))),
        ),
    );

    assert!(alpha_eq_prop(&left, &right));
    assert!(!alpha_eq_prop(
        &equal(Term::Var(Symbol(1)), Term::Var(Symbol(2))),
        &equal(Term::Var(Symbol(1)), Term::Var(Symbol(11))),
    ));
}

#[test]
fn alpha_eq_term_renames_lambda_and_list_case_binders() {
    let left = lambda(
        Symbol(1),
        list_case(
            Term::Var(Symbol(9)),
            Term::Nil,
            Symbol(2),
            apply(Term::Var(Symbol(1)), Term::Var(Symbol(2))),
        ),
    );
    let right = lambda(
        Symbol(10),
        list_case(
            Term::Var(Symbol(9)),
            Term::Nil,
            Symbol(20),
            apply(Term::Var(Symbol(10)), Term::Var(Symbol(20))),
        ),
    );
    let reversed = lambda(
        Symbol(10),
        list_case(
            Term::Var(Symbol(9)),
            Term::Nil,
            Symbol(20),
            apply(Term::Var(Symbol(20)), Term::Var(Symbol(10))),
        ),
    );

    assert!(alpha_eq_term(&left, &right));
    assert!(!alpha_eq_term(&left, &reversed));
    assert!(!alpha_eq_term(
        &lambda(Symbol(1), Term::Quote(Symbol(1))),
        &lambda(Symbol(2), Term::Quote(Symbol(2))),
    ));
}

#[test]
fn checker_accepts_alpha_equivalent_goal() {
    let proof = Proof::ForAllIntro {
        variable: Symbol(1),
        proof: Box::new(Proof::Refl(Term::Var(Symbol(1)))),
    };
    let expected = forall(Symbol(2), equal(Term::Var(Symbol(2)), Term::Var(Symbol(2))));

    assert!(check(&proof, &expected));
}

#[test]
fn step_beta_reduces_after_argument_is_ready() {
    let term = apply(
        lambda(Symbol(1), Term::Var(Symbol(1))),
        Term::Quote(Symbol(2)),
    );

    assert_eq!(step(&term), Step::Reduced(Term::Quote(Symbol(2))));
}

#[test]
fn application_reduces_argument_before_beta() {
    let term = apply(
        lambda(Symbol(1), Term::Quote(Symbol(9))),
        apply(
            lambda(Symbol(2), Term::Var(Symbol(2))),
            Term::Quote(Symbol(3)),
        ),
    );

    assert_eq!(
        step(&term),
        Step::Reduced(apply(
            lambda(Symbol(1), Term::Quote(Symbol(9))),
            Term::Quote(Symbol(3))
        ))
    );
    assert_eq!(normal_form(&term), Term::Quote(Symbol(9)));
}

#[test]
fn lambda_is_a_value_without_evaluating_body() {
    let term = lambda(
        Symbol(1),
        apply(
            lambda(Symbol(2), Term::Var(Symbol(2))),
            Term::Var(Symbol(1)),
        ),
    );

    assert_eq!(step(&term), Step::Normal);
}

#[test]
fn is_value_distinguishes_values_from_pending_computations() {
    assert!(term_is_value(&Term::Nil));
    assert!(term_is_value(&Term::Quote(Symbol(1))));
    assert!(term_is_value(&lambda(Symbol(1), Term::Var(Symbol(1)))));
    assert!(term_is_value(&cons(Term::Quote(Symbol(1)), Term::Nil)));

    assert!(!term_is_value(&apply(
        Term::Var(Symbol(1)),
        Term::Quote(Symbol(2))
    )));
    assert!(!term_is_value(&Term::Diverge));
    assert!(!term_is_value(&error(Term::Quote(Symbol(1)))));
    assert!(!term_is_value(&Term::Var(Symbol(1))));
    assert_eq!(step(&Term::Var(Symbol(1))), Step::Normal);
}

#[test]
fn application_propagates_effects() {
    let thrown = error(Term::Quote(Symbol(1)));

    assert_eq!(
        normal_form(&apply(thrown.clone(), Term::Quote(Symbol(2)))),
        thrown.clone()
    );
    assert_eq!(
        normal_form(&apply(
            lambda(Symbol(1), Term::Quote(Symbol(2))),
            thrown.clone()
        )),
        thrown
    );
    assert_eq!(
        normal_form(&apply(
            lambda(Symbol(1), Term::Quote(Symbol(2))),
            Term::Diverge
        )),
        Term::Diverge
    );
}

#[test]
fn apply_known_non_callable_reduces_to_error() {
    let term = apply(Term::Nil, Term::Quote(Symbol(2)));

    assert_eq!(step(&term), Step::Reduced(error(Term::Nil)));
}

#[test]
fn cons_evaluates_head_then_tail_and_propagates_effects() {
    let term = cons(
        apply(
            lambda(Symbol(1), Term::Var(Symbol(1))),
            Term::Quote(Symbol(2)),
        ),
        error(Term::Quote(Symbol(3))),
    );

    assert_eq!(
        step(&term),
        Step::Reduced(cons(Term::Quote(Symbol(2)), error(Term::Quote(Symbol(3)))))
    );
    assert_eq!(normal_form(&term), error(Term::Quote(Symbol(3))));
}

#[test]
fn head_and_tail_destructure_cons() {
    let term = cons(Term::Quote(Symbol(1)), Term::Quote(Symbol(2)));

    assert_eq!(
        step(&head(term.clone())),
        Step::Reduced(Term::Quote(Symbol(1)))
    );
    assert_eq!(step(&tail(term)), Step::Reduced(Term::Quote(Symbol(2))));
}

#[test]
fn head_and_tail_open_terms_are_neutral() {
    assert_eq!(step(&head(Term::Var(Symbol(1)))), Step::Normal);
    assert_eq!(step(&tail(Term::Var(Symbol(1)))), Step::Normal);
}

#[test]
fn head_and_tail_known_non_cons_reduce_to_error() {
    assert_eq!(step(&head(Term::Nil)), Step::Reduced(error(Term::Nil)));
    assert_eq!(step(&tail(Term::Nil)), Step::Reduced(error(Term::Nil)));
}

#[test]
fn list_case_reduces_nil_and_cons() {
    let cons_value = cons(Term::Quote(Symbol(1)), Term::Nil);
    let cons_case = head(Term::Var(Symbol(9)));

    assert_eq!(
        step(&list_case(
            Term::Nil,
            Term::Quote(Symbol(0)),
            Symbol(9),
            cons_case.clone(),
        )),
        Step::Reduced(Term::Quote(Symbol(0)))
    );
    assert_eq!(
        normal_form(&list_case(
            cons_value,
            Term::Quote(Symbol(0)),
            Symbol(9),
            cons_case,
        )),
        Term::Quote(Symbol(1))
    );
}

#[test]
fn list_case_open_term_is_neutral_and_known_non_list_reduces_to_error() {
    assert_eq!(
        step(&list_case(
            Term::Var(Symbol(1)),
            Term::Quote(Symbol(0)),
            Symbol(9),
            Term::Quote(Symbol(1)),
        )),
        Step::Normal
    );
    assert_eq!(
        step(&list_case(
            Term::Quote(Symbol(1)),
            Term::Quote(Symbol(0)),
            Symbol(9),
            Term::Quote(Symbol(1))
        )),
        Step::Reduced(error(Term::Quote(Symbol(1))))
    );
}

#[test]
fn substitution_descends_into_cons_and_destructors() {
    let term = cons(head(Term::Var(Symbol(1))), tail(Term::Var(Symbol(2))));

    assert_eq!(
        substitute(&term, Symbol(1), &Term::Quote(Symbol(3))),
        cons(head(Term::Quote(Symbol(3))), tail(Term::Var(Symbol(2))))
    );
}

#[test]
fn substitution_avoids_lambda_capture() {
    let term = lambda(Symbol(2), Term::Var(Symbol(1)));

    assert_eq!(
        substitute(&term, Symbol(1), &Term::Var(Symbol(2))),
        lambda(Symbol(0), Term::Var(Symbol(2)))
    );
}

#[test]
fn substitution_avoids_list_case_capture() {
    let term = list_case(
        Term::Var(Symbol(1)),
        Term::Quote(Symbol(0)),
        Symbol(2),
        Term::Var(Symbol(3)),
    );

    assert_eq!(
        substitute(&term, Symbol(3), &Term::Var(Symbol(2))),
        list_case(
            Term::Var(Symbol(1)),
            Term::Quote(Symbol(0)),
            Symbol(4),
            Term::Var(Symbol(2))
        )
    );
}

#[test]
fn free_symbols_ignore_list_case_cons_binder() {
    assert_eq!(
        free_symbols(&list_case(
            Term::Var(Symbol(1)),
            Term::Var(Symbol(2)),
            Symbol(3),
            apply(Term::Var(Symbol(3)), Term::Var(Symbol(4)))
        )),
        HashSet::from([Symbol(1), Symbol(2), Symbol(4)])
    );
}

#[test]
fn step_proof_proves_one_step_reduction() {
    let term = head(cons(Term::Quote(Symbol(1)), Term::Nil));

    assert!(check(
        &Proof::Step(term.clone()),
        &equal(term, Term::Quote(Symbol(1)))
    ));
}

#[test]
fn steps_proof_proves_multi_step_reduction() {
    let start = apply(
        lambda(Symbol(1), Term::Quote(Symbol(9))),
        apply(
            lambda(Symbol(2), Term::Var(Symbol(2))),
            Term::Quote(Symbol(3)),
        ),
    );
    let middle = apply(
        lambda(Symbol(1), Term::Quote(Symbol(9))),
        Term::Quote(Symbol(3)),
    );
    let end = Term::Quote(Symbol(9));

    assert!(check(
        &Proof::Steps(vec![start.clone(), middle, end.clone()]),
        &equal(start, end)
    ));
}

#[test]
fn theorem_from_proof_checks_closed_proofs() {
    let valid = Theorem::from_proof(
        Proof::Refl(Term::Quote(Symbol(1))),
        equal(Term::Quote(Symbol(1)), Term::Quote(Symbol(1))),
    );
    let invalid = Theorem::from_proof(
        Proof::Refl(Term::Quote(Symbol(1))),
        equal(Term::Quote(Symbol(1)), Term::Quote(Symbol(2))),
    );

    assert!(valid.is_some());
    assert!(invalid.is_none());
    assert!(
        Theorem::from_proof(
            Proof::Assume(Symbol(7)),
            equal(Term::Quote(Symbol(1)), Term::Quote(Symbol(1)))
        )
        .is_none()
    );
}

#[test]
fn theory_known_proofs_cite_named_theorems() {
    let name = Name(42);
    let theorem = Theorem::refl(Term::Quote(Symbol(1)));
    let replacement = Theorem::refl(Term::Quote(Symbol(2)));
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
fn theory_defines_closed_terms() {
    let name = Name(4);
    let term = Term::Quote(Symbol(1));
    let replacement = Term::Quote(Symbol(2));
    let theorem = Theorem::refl(Term::Nil);
    let mut theory = Theory::new();

    assert!(theory.define_term(name, &term));
    assert_eq!(theory.term(name), Some(&term));
    assert!(!theory.define_term(name, &replacement));
    assert!(!theory.define_theorem(name, &theorem));
    assert!(!theory.define_term(Name(5), &Term::Var(Symbol(1))));

    assert!(theory.define_theorem(Name(6), &theorem));
    assert!(!theory.define_term(Name(6), &Term::Nil));
}

#[test]
fn term_definitions_unfold_during_evaluation() {
    let id = Name(8);
    let id_term = lambda(Symbol(1), Term::Var(Symbol(1)));
    let argument = Term::Quote(Symbol(2));
    let call = apply(Term::Const(id), argument.clone());
    let mut theory = Theory::new();

    assert_eq!(step(&Term::Const(id)), Step::Normal);
    assert_eq!(
        step(&apply(Term::Const(Name(9)), argument.clone())),
        Step::Normal
    );

    assert!(theory.define_term(id, &id_term));
    assert_eq!(
        theory.reduce(&Term::Const(id)),
        Step::Reduced(id_term.clone())
    );
    assert_eq!(theory.normal_form(&call), argument.clone());
    assert_eq!(normal_form(&call), call);
}

#[test]
fn step_proofs_use_bindings_term_definitions() {
    let name = Name(11);
    let term = Term::Const(name);
    let value = Term::Quote(Symbol(7));
    let mut theory = Theory::new();

    assert!(theory.define_term(name, &value));
    assert!(theory.check(
        &Proof::Step(term.clone()),
        &equal(term.clone(), value.clone())
    ));
    assert!(!check(
        &Proof::Step(term.clone()),
        &equal(term.clone(), value.clone())
    ));

    let theorem = theory
        .step(term.clone())
        .expect("defined constant should step");
    assert_eq!(theorem.prop(), &equal(term, value));
}

#[test]
fn raw_checker_known_proofs_compose_with_rules() {
    let start = head(cons(Term::Quote(Symbol(1)), Term::Nil));
    let end = Term::Quote(Symbol(1));
    let step = Theorem::step(start.clone()).expect("term should step");
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
    let start = head(cons(Term::Quote(Symbol(1)), Term::Nil));
    let end = Term::Quote(Symbol(1));
    let step = Theorem::step(start.clone()).expect("term should step");
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
        lambda(Symbol(1), Term::Var(Symbol(1))),
        Term::Quote(Symbol(2)),
    );
    let step = Theorem::step(start.clone()).expect("term should step");
    let refl = Theorem::refl(Term::Quote(Symbol(2)));
    let trans = Theorem::trans(&step, &refl).expect("equalities should chain");
    let symm = Theorem::symm(&step).expect("step equality should be symmetric");

    assert_eq!(step.prop(), &equal(start.clone(), Term::Quote(Symbol(2))));
    assert_eq!(trans.prop(), &equal(start.clone(), Term::Quote(Symbol(2))));
    assert_eq!(symm.prop(), &equal(Term::Quote(Symbol(2)), start));
    assert!(Theorem::step(Term::Quote(Symbol(2))).is_none());
}

#[test]
fn theorem_rewrite_moves_props_across_equality() {
    let term = apply(lambda(Symbol(1), Term::Var(Symbol(1))), Term::Nil);
    let step = Theorem::step(term.clone()).expect("term should step");
    let nil_to_term = Theorem::symm(&step).expect("step should be symmetric");
    let theorem = Theorem::rewrite(
        &nil_to_term,
        &Theorem::list_nil(),
        Symbol(99),
        is_list(Term::Var(Symbol(99))),
    )
    .expect("rewrite should prove listness before evaluation");

    assert_eq!(theorem.prop(), &is_list(term));
}

#[test]
fn theorem_value_and_list_rules_build_checked_theorems() {
    let head = Term::Quote(Symbol(1));
    let tail = Term::Nil;
    let head_value = Theorem::value_quote(Symbol(1));
    let tail_value = Theorem::value_nil();
    let tail_list = Theorem::list_nil();
    let list = cons(head.clone(), tail.clone());
    let value = Theorem::value_cons(head.clone(), tail.clone(), &head_value, &tail_value)
        .expect("cons of values is a value");
    let list_theorem = Theorem::list_cons(head.clone(), tail.clone(), &head_value, &tail_list)
        .expect("cons with value head and list tail is a list");

    assert_eq!(value.prop(), &is_value(list.clone()));
    assert_eq!(list_theorem.prop(), &is_list(list));
    assert!(Theorem::list_cons(Term::Diverge, tail, &head_value, &tail_list).is_none());
}

#[test]
fn theorem_first_order_rules_build_checked_theorems() {
    let prop = equal(Term::Quote(Symbol(1)), Term::Quote(Symbol(1)));
    let implication = Theorem::from_proof(
        Proof::ImpliesIntro {
            assumption: Symbol(7),
            premise: prop.clone(),
            proof: Box::new(Proof::Assume(Symbol(7))),
        },
        implies(prop.clone(), prop.clone()),
    )
    .expect("identity implication should check");
    let conclusion = Theorem::implies_elim(&implication, &Theorem::refl(Term::Quote(Symbol(1))))
        .expect("modus ponens should apply");
    let universal = Theorem::from_proof(
        Proof::ForAllIntro {
            variable: Symbol(1),
            proof: Box::new(Proof::Refl(Term::Var(Symbol(1)))),
        },
        forall(Symbol(1), equal(Term::Var(Symbol(1)), Term::Var(Symbol(1)))),
    )
    .expect("forall intro should check");
    let instance = Theorem::forall_elim(&universal, Term::Quote(Symbol(2)))
        .expect("forall theorem should instantiate");

    assert_eq!(conclusion.prop(), &prop);
    assert_eq!(
        instance.prop(),
        &equal(Term::Quote(Symbol(2)), Term::Quote(Symbol(2)))
    );
}

#[test]
fn rewrite_uses_equality_inside_template() {
    let start = head(cons(Term::Quote(Symbol(1)), Term::Nil));
    let end = Term::Quote(Symbol(1));
    let template = equal(
        cons(Term::Var(Symbol(99)), Term::Nil),
        cons(Term::Var(Symbol(99)), Term::Nil),
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
        body: Box::new(Term::Quote(Symbol(9))),
    };
    let argument = apply(
        lambda(Symbol(2), Term::Var(Symbol(2))),
        Term::Quote(Symbol(3)),
    );

    assert!(!check(
        &Proof::Beta {
            lambda: lam.clone(),
            argument: argument.clone()
        },
        &Prop::Equal(apply(Term::Lambda(lam), argument), Term::Quote(Symbol(9)))
    ));
}

#[test]
fn value_intro_rules_prove_concrete_values() {
    let lambda = Lambda {
        parameter: Symbol(1),
        body: Box::new(Term::Var(Symbol(1))),
    };
    let list = cons(Term::Quote(Symbol(1)), Term::Nil);
    let proof = Proof::ValueCons {
        head: Term::Quote(Symbol(1)),
        tail: Term::Nil,
        head_is_value: Box::new(Proof::ValueQuote(Symbol(1))),
        tail_is_value: Box::new(Proof::ValueNil),
    };

    assert!(check(
        &Proof::ValueLambda(lambda.clone()),
        &is_value(Term::Lambda(lambda))
    ));
    assert!(check(
        &Proof::ValueQuote(Symbol(1)),
        &is_value(Term::Quote(Symbol(1)))
    ));
    assert!(check(&Proof::ValueNil, &is_value(Term::Nil)));
    assert!(check(&proof, &is_value(list)));
}

#[test]
fn value_cons_requires_matching_value_proofs() {
    let proof = Proof::ValueCons {
        head: Term::Diverge,
        tail: Term::Nil,
        head_is_value: Box::new(Proof::ValueQuote(Symbol(1))),
        tail_is_value: Box::new(Proof::ValueNil),
    };

    assert!(!check(&proof, &is_value(cons(Term::Diverge, Term::Nil))));
}

#[test]
fn list_intro_rules_prove_concrete_lists() {
    let list = cons(
        Term::Quote(Symbol(1)),
        cons(Term::Quote(Symbol(2)), Term::Nil),
    );
    let proof = Proof::ListCons {
        head: Term::Quote(Symbol(1)),
        tail: cons(Term::Quote(Symbol(2)), Term::Nil),
        head_is_value: Box::new(Proof::ValueQuote(Symbol(1))),
        tail_is_list: Box::new(Proof::ListCons {
            head: Term::Quote(Symbol(2)),
            tail: Term::Nil,
            head_is_value: Box::new(Proof::ValueQuote(Symbol(2))),
            tail_is_list: Box::new(Proof::ListNil),
        }),
    };

    assert!(check(&Proof::ListNil, &is_list(Term::Nil)));
    assert!(check(&proof, &is_list(list)));
}

#[test]
fn list_cons_requires_tail_list_proof_for_the_same_tail() {
    let proof = Proof::ListCons {
        head: Term::Quote(Symbol(1)),
        tail: cons(Term::Quote(Symbol(2)), Term::Nil),
        head_is_value: Box::new(Proof::ValueQuote(Symbol(1))),
        tail_is_list: Box::new(Proof::ListNil),
    };

    assert!(!check(
        &proof,
        &is_list(cons(
            Term::Quote(Symbol(1)),
            cons(Term::Quote(Symbol(2)), Term::Nil)
        ))
    ));
}

#[test]
fn list_cons_requires_head_value_proof_for_the_same_head() {
    let proof = Proof::ListCons {
        head: Term::Diverge,
        tail: Term::Nil,
        head_is_value: Box::new(Proof::ValueQuote(Symbol(1))),
        tail_is_list: Box::new(Proof::ListNil),
    };

    assert!(!check(&proof, &is_list(cons(Term::Diverge, Term::Nil))));
}

#[test]
fn is_list_can_be_rewritten_back_across_evaluation() {
    let term = apply(lambda(Symbol(1), Term::Var(Symbol(1))), Term::Nil);
    let proof = Proof::Rewrite {
        equality: Box::new(Proof::Symm(Box::new(Proof::Step(term.clone())))),
        proof: Box::new(Proof::ListNil),
        variable: Symbol(99),
        template: is_list(Term::Var(Symbol(99))),
    };

    assert!(check(&proof, &is_list(term)));
}

#[test]
fn list_induction_proves_every_list_is_a_value() {
    let variable = Symbol(1);
    let head = Symbol(2);
    let tail = Symbol(3);
    let head_is_value_assumption = Symbol(4);
    let tail_is_list_assumption = Symbol(5);
    let induction_hypothesis_assumption = Symbol(6);
    let property = is_value(Term::Var(variable));
    let proof = Proof::ListInduction {
        variable,
        property: property.clone(),
        base: Box::new(Proof::ValueNil),
        head,
        tail,
        head_is_value_assumption,
        tail_is_list_assumption,
        induction_hypothesis_assumption,
        step: Box::new(Proof::ValueCons {
            head: Term::Var(head),
            tail: Term::Var(tail),
            head_is_value: Box::new(Proof::Assume(head_is_value_assumption)),
            tail_is_value: Box::new(Proof::Assume(induction_hypothesis_assumption)),
        }),
    };
    let expected = forall(
        variable,
        implies(is_list(Term::Var(variable)), is_value(Term::Var(variable))),
    );

    assert!(check(&proof, &expected));
}

#[test]
fn list_induction_rejects_stale_step_variables() {
    let variable = Symbol(1);
    let head = Symbol(2);
    let tail = Symbol(3);
    let head_is_value_assumption = Symbol(4);
    let tail_is_list_assumption = Symbol(5);
    let induction_hypothesis_assumption = Symbol(6);
    let property = is_list(Term::Var(variable));
    let proof = Proof::ListInduction {
        variable,
        property,
        base: Box::new(Proof::ListNil),
        head,
        tail,
        head_is_value_assumption,
        tail_is_list_assumption,
        induction_hypothesis_assumption,
        step: Box::new(Proof::Assume(tail_is_list_assumption)),
    };
    let expected = forall(
        variable,
        implies(is_list(Term::Var(variable)), is_list(Term::Var(variable))),
    );

    assert!(!check(&proof, &expected));
}

#[test]
fn assume_uses_context() {
    let prop = equal(Term::Quote(Symbol(1)), Term::Quote(Symbol(1)));
    let mut context = Context::new();
    context.insert(Symbol(7), prop.clone());

    assert!(check_in_context(&Proof::Assume(Symbol(7)), &prop, &context));
    assert!(!check(&Proof::Assume(Symbol(7)), &prop));
}

#[test]
fn implies_intro_and_elim_work() {
    let prop = equal(Term::Quote(Symbol(1)), Term::Quote(Symbol(1)));
    let proof = Proof::ImpliesElim {
        implication: Box::new(Proof::ImpliesIntro {
            assumption: Symbol(7),
            premise: prop.clone(),
            proof: Box::new(Proof::Assume(Symbol(7))),
        }),
        premise: Box::new(Proof::Refl(Term::Quote(Symbol(1)))),
    };

    assert!(check(&proof, &prop));
}

#[test]
fn forall_intro_and_elim_work() {
    let proof = Proof::ForAllElim {
        forall: Box::new(Proof::ForAllIntro {
            variable: Symbol(1),
            proof: Box::new(Proof::Refl(Term::Var(Symbol(1)))),
        }),
        argument: Term::Quote(Symbol(2)),
    };

    assert!(check(
        &proof,
        &equal(Term::Quote(Symbol(2)), Term::Quote(Symbol(2)))
    ));
}

#[test]
fn exists_intro_and_elim_work() {
    let body = equal(Term::Var(Symbol(1)), Term::Var(Symbol(1)));
    let conclusion = equal(Term::Quote(Symbol(0)), Term::Quote(Symbol(0)));
    let proof = Proof::ExistsElim {
        existential: Box::new(Proof::ExistsIntro {
            variable: Symbol(1),
            body,
            witness: Term::Quote(Symbol(2)),
            proof: Box::new(Proof::Refl(Term::Quote(Symbol(2)))),
        }),
        witness: Symbol(9),
        assumption: Symbol(7),
        proof: Box::new(Proof::Refl(Term::Quote(Symbol(0)))),
    };

    assert!(check(&proof, &conclusion));
}

#[test]
fn and_or_rules_work() {
    let left = equal(Term::Quote(Symbol(1)), Term::Quote(Symbol(1)));
    let right = equal(Term::Quote(Symbol(2)), Term::Quote(Symbol(2)));
    let and_proof = Proof::AndIntro(
        Box::new(Proof::Refl(Term::Quote(Symbol(1)))),
        Box::new(Proof::Refl(Term::Quote(Symbol(2)))),
    );

    assert!(check(
        &Proof::AndElimLeft(Box::new(and_proof.clone())),
        &left
    ));
    assert!(check(&Proof::AndElimRight(Box::new(and_proof)), &right));

    let or_proof = Proof::OrElim {
        disjunction: Box::new(Proof::OrIntroLeft {
            proof: Box::new(Proof::Refl(Term::Quote(Symbol(1)))),
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
    let prop = forall(Symbol(2), equal(Term::Var(Symbol(1)), Term::Var(Symbol(2))));

    assert_eq!(
        substitute_prop(&prop, Symbol(1), &Term::Var(Symbol(2))),
        forall(Symbol(0), equal(Term::Var(Symbol(2)), Term::Var(Symbol(0))))
    );
}

#[test]
fn exists_intro_uses_witness() {
    let body = equal(Term::Var(Symbol(1)), Term::Var(Symbol(1)));
    let proof = Proof::ExistsIntro {
        variable: Symbol(1),
        body: body.clone(),
        witness: Term::Quote(Symbol(2)),
        proof: Box::new(Proof::Refl(Term::Quote(Symbol(2)))),
    };

    assert!(check(&proof, &exists(Symbol(1), body)));
}

#[test]
fn prop_helpers_construct_expected_shapes() {
    let prop = equal(Term::Quote(Symbol(1)), Term::Quote(Symbol(1)));
    let term = apply(
        lambda(Symbol(1), Term::Var(Symbol(1))),
        Term::Quote(Symbol(2)),
    );

    assert_eq!(
        implies(prop.clone(), prop.clone()),
        Prop::Implies(Box::new(prop.clone()), Box::new(prop))
    );
    assert_eq!(
        terminates(Symbol(9), term.clone()),
        exists(
            Symbol(9),
            and(
                computes_to(term.clone(), Term::Var(Symbol(9))),
                is_value(Term::Var(Symbol(9))),
            ),
        )
    );
    assert_eq!(
        computes_to_list(Symbol(9), term.clone()),
        exists(
            Symbol(9),
            and(
                computes_to(term.clone(), Term::Var(Symbol(9))),
                is_list(Term::Var(Symbol(9)))
            ),
        )
    );
    assert_eq!(
        errors(Symbol(9), term.clone()),
        exists(
            Symbol(9),
            computes_to(term.clone(), Term::Error(Box::new(Term::Var(Symbol(9))))),
        )
    );
    assert_eq!(diverges(term.clone()), computes_to(term, Term::Diverge));
    assert_eq!(
        or(is_value(Term::Quote(Symbol(1))), is_list(Term::Nil)),
        Prop::Or(
            Box::new(Prop::IsValue(Term::Quote(Symbol(1)))),
            Box::new(Prop::IsList(Term::Nil))
        )
    );
}
