use click::{self, Object, Term, run_source};

fn sym(name: &str) -> Term {
    Term::symbol(name)
}

fn tagged_payload<'a>(term: &'a Term, tag: &str) -> &'a Term {
    let object = term.as_object().expect("expected an object");
    object.get(tag).expect("missing expected tag")
}

fn identity_expr() -> Term {
    click::apply(click::lambda(":x", click::var(":x")), sym(":ok"))
}

fn identity_proof() -> Term {
    let step = click::cek_step_proof();
    click::cek_next_proof(
        step.clone(),
        click::cek_next_proof(
            step.clone(),
            click::cek_next_proof(
                step.clone(),
                click::cek_next_proof(
                    step.clone(),
                    click::cek_next_proof(
                        step.clone(),
                        click::cek_next_proof(
                            step.clone(),
                            click::cek_return_proof(step, click::object_equal_proof()),
                        ),
                    ),
                ),
            ),
        ),
    )
}

#[test]
fn eval_returns_symbols_as_values() {
    assert_eq!(
        click::eval(&sym(":ok")).expect("eval should succeed"),
        sym(":ok")
    );
}

#[test]
fn parse_turns_key_value_lists_into_nested_objects() {
    let expected: Term = Object::new()
        .with(":foo", sym(":bar"))
        .with(":nested", Object::new().with(":x", sym(":y")).into())
        .into();

    assert_eq!(
        click::parse("(:foo :bar :nested (:x :y))").expect("parse should succeed"),
        expected
    );
}

#[test]
fn parse_many_reads_multiple_terms() {
    assert_eq!(
        click::parse_many(":a\n(:b :c)")
            .expect("parse_many should succeed")
            .len(),
        2
    );
}

#[test]
fn parse_can_express_the_cek_identity_program() {
    let source = "(:apply (:function (:lambda (:param :x :body (:var :x))) :arg :ok))";

    assert_eq!(
        click::eval(&click::parse(source).expect("parse should succeed"))
            .expect("eval should succeed"),
        sym(":ok")
    );
}

#[test]
fn parse_rejects_malformed_objects() {
    assert_eq!(
        click::parse("(:foo)").expect_err("odd object should fail"),
        "objects must contain key/value pairs"
    );
    assert_eq!(
        click::parse("((:x :y) :z)").expect_err("non-symbol key should fail"),
        "object keys must be symbols"
    );
}

#[test]
fn var_reads_from_the_explicit_environment() {
    let env: Term = Object::new().with(":x", sym(":value")).into();

    assert_eq!(
        click::eval_in_env(&click::var(":x"), &env).expect("eval should succeed"),
        sym(":value")
    );
}

#[test]
fn lambda_application_uses_lexical_closure_capture() {
    let env: Term = Object::new().with(":captured", sym(":outer")).into();
    let expr = click::apply(
        click::lambda(":x", click::var(":captured")),
        sym(":ignored"),
    );

    assert_eq!(
        click::eval_in_env(&expr, &env).expect("eval should succeed"),
        sym(":outer")
    );
}

#[test]
fn cek_step_returns_explicit_next_and_return_outcomes() {
    let first = click::cek_step(&click::initial_state(sym(":ok"))).expect("step should succeed");
    let next_state = tagged_payload(&first, ":next").clone();
    let second = click::cek_step(&next_state).expect("step should succeed");

    assert_eq!(tagged_payload(&second, ":return"), &sym(":ok"));
}

#[test]
fn cek_step_reports_bad_states_as_error_outcomes() {
    let error = click::cek_step(&sym(":not-a-state")).expect("step should succeed");
    assert!(
        tagged_payload(&error, ":error")
            .as_object()
            .expect("error should be structured")
            .has(":bad_eval_state")
    );
}

#[test]
fn applying_a_non_closure_is_an_error() {
    assert_eq!(
        click::eval(&click::apply(sym(":not-a-function"), sym(":arg")))
            .expect_err("applying a bare symbol should fail"),
        "{:not-a-function :not-a-function}"
    );
}

#[test]
fn check_proves_structural_object_equality() {
    let left: Term = Object::new().with(":x", sym(":ok")).into();
    let claim = click::object_equal_claim(left.clone(), left);
    let checked = click::check(&claim, &click::object_equal_proof());

    assert_eq!(tagged_payload(&checked, ":ok"), &claim);
}

#[test]
fn check_proves_one_cek_step_by_running_the_stepper() {
    let input = click::initial_state(sym(":ok"));
    let output = click::cek_step(&input).expect("step should succeed");
    let claim = click::cek_step_equals_claim(input, output);
    let checked = click::check(&claim, &click::cek_step_proof());

    assert_eq!(tagged_payload(&checked, ":ok"), &claim);
}

#[test]
fn check_proves_cek_evals_to_with_a_nested_trace_proof() {
    let claim = click::cek_evals_to_claim(click::initial_state(identity_expr()), sym(":ok"));
    let checked = click::check(&claim, &identity_proof());

    assert_eq!(tagged_payload(&checked, ":ok"), &claim);
}

#[test]
fn check_rejects_a_false_eval_claim() {
    let claim = click::cek_evals_to_claim(click::initial_state(identity_expr()), sym(":wrong"));
    let checked = click::check(&claim, &identity_proof());

    assert!(
        tagged_payload(&checked, ":error")
            .as_object()
            .expect("error should be structured")
            .has(":object-not-equal")
    );
}

#[test]
fn run_source_ignores_shebang_and_returns_the_last_value() {
    assert_eq!(
        run_source("#!/usr/bin/env click\n:first\n:done\n")
            .expect("run_source should succeed")
            .expect("source should produce a value"),
        sym(":done")
    );
}

#[test]
fn run_source_returns_none_for_empty_input() {
    assert_eq!(run_source("").expect("empty source should parse"), None);
}
