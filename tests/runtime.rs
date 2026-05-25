use click::{self, Object, Term, run_source};

fn sym(name: &str) -> Term {
    Term::symbol(name)
}

fn tagged_payload<'a>(term: &'a Term, tag: &str) -> &'a Term {
    let object = term.as_object().expect("expected an object");
    object.get(tag).expect("missing expected tag")
}

fn identity_expr() -> Term {
    click::apply(
        click::lambda(":x", click::var(":x")),
        click::quote(sym(":ok")),
    )
}

fn identity_proof() -> Term {
    let step = click::step_proof();
    click::returns_next_proof(
        step.clone(),
        click::returns_next_proof(
            step.clone(),
            click::returns_next_proof(
                step.clone(),
                click::returns_next_proof(
                    step.clone(),
                    click::returns_next_proof(
                        step.clone(),
                        click::returns_next_proof(
                            step.clone(),
                            click::returns_return_proof(step, click::equal_structural_proof()),
                        ),
                    ),
                ),
            ),
        ),
    )
}

#[test]
fn eval_requires_explicit_quote_for_literal_values() {
    assert_eq!(
        click::eval(&click::quote(sym(":ok"))).expect("eval should succeed"),
        sym(":ok")
    );

    assert_eq!(
        click::eval(&sym(":ok")).expect_err("bare symbols are not expressions"),
        "(:not-an-expr :ok)"
    );
}

#[test]
fn quote_returns_record_values() {
    let record: Term = Object::new().with(":answer", sym(":ok")).into();
    assert_eq!(
        click::eval(&click::quote(record.clone())).expect("eval should succeed"),
        record
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
fn display_uses_parseable_object_syntax() {
    let term: Term = Object::new()
        .with(":foo", sym(":bar"))
        .with(":nested", Object::new().with(":x", sym(":y")).into())
        .into();

    assert_eq!(term.to_string(), "(:foo :bar :nested (:x :y))");
    assert_eq!(
        click::parse(&term.to_string()).expect("displayed object should parse"),
        term
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
fn parse_can_express_the_quoted_identity_program() {
    let source = "(:apply (:function (:lambda (:param :x :body (:var :x))) :arg (:quote :ok)))";

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
        click::quote(sym(":ignored")),
    );

    assert_eq!(
        click::eval_in_env(&expr, &env).expect("eval should succeed"),
        sym(":outer")
    );
}

#[test]
fn object_operations_read_update_test_compare_and_branch() {
    let base: Term = Object::new().with(":answer", sym(":ok")).into();

    assert_eq!(
        click::eval(&click::get(click::quote(base.clone()), ":answer"))
            .expect("get should succeed"),
        sym(":ok")
    );

    let updated = click::eval(&click::with(
        click::quote(base.clone()),
        ":extra",
        click::quote(sym(":yes")),
    ))
    .expect("with should succeed");
    assert_eq!(
        updated.as_object().and_then(|object| object.get(":extra")),
        Some(&sym(":yes"))
    );

    assert_eq!(
        click::eval(&click::has(click::quote(base.clone()), ":answer"))
            .expect("has should succeed"),
        sym(":true")
    );
    assert_eq!(
        click::eval(&click::equal(
            click::quote(sym(":same")),
            click::quote(sym(":same"))
        ))
        .expect("equal should succeed"),
        sym(":true")
    );
    assert_eq!(
        click::eval(&click::if_expr(
            click::quote(sym(":true")),
            click::quote(sym(":then")),
            click::quote(sym(":else")),
        ))
        .expect("if should succeed"),
        sym(":then")
    );
}

#[test]
fn object_operations_report_errors() {
    assert_eq!(
        click::eval(&click::get(click::quote(sym(":not-record")), ":x"))
            .expect_err("get on a symbol should fail"),
        "(:not-a-record :not-record)"
    );

    let empty: Term = Object::new().into();
    assert_eq!(
        click::eval(&click::get(click::quote(empty), ":missing"))
            .expect_err("missing field should fail"),
        "(:missing-field :missing)"
    );

    assert_eq!(
        click::eval(&click::if_expr(
            click::quote(sym(":maybe")),
            click::quote(sym(":then")),
            click::quote(sym(":else")),
        ))
        .expect_err("non-boolean condition should fail"),
        "(:bad-condition :maybe)"
    );
}

#[test]
fn cek_step_returns_explicit_next_and_return_outcomes() {
    let first =
        click::cek_step(&click::initial_state(click::quote(sym(":ok")))).expect("step should run");
    let next_state = tagged_payload(&first, ":next").clone();
    let second = click::cek_step(&next_state).expect("step should run");

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
        click::eval(&click::apply(
            click::quote(sym(":not-a-function")),
            click::quote(sym(":arg")),
        ))
        .expect_err("applying a bare symbol should fail"),
        "(:not-a-function :not-a-function)"
    );
}

#[test]
fn check_proves_structural_object_equality() {
    let left: Term = Object::new().with(":x", sym(":ok")).into();
    let claim = click::equal_claim(left.clone(), left);
    let checked = click::check(&claim, &click::equal_structural_proof());

    assert_eq!(checked, sym(":ok"));
}

#[test]
fn check_proves_one_cek_step_by_running_the_stepper() {
    let input = click::initial_state(click::quote(sym(":ok")));
    let output = click::cek_step(&input).expect("step should succeed");
    let claim = click::step_equals_claim(input, output);
    let checked = click::check(&claim, &click::step_proof());

    assert_eq!(checked, sym(":ok"));
}

#[test]
fn check_proves_returns_with_a_nested_trace_proof() {
    let claim = click::returns_claim(click::initial_state(identity_expr()), sym(":ok"));
    let checked = click::check(&claim, &identity_proof());

    assert_eq!(checked, sym(":ok"));
}

#[test]
fn check_rejects_a_false_returns_claim() {
    let claim = click::returns_claim(click::initial_state(identity_expr()), sym(":wrong"));
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
        run_source("#!/usr/bin/env click\n(:quote :first)\n(:quote :done)\n")
            .expect("run_source should succeed")
            .expect("source should produce a value"),
        sym(":done")
    );
}

#[test]
fn run_source_returns_none_for_empty_input() {
    assert_eq!(run_source("").expect("empty source should parse"), None);
}
