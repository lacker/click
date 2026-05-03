use click::{self, Object, Term, run_source};

fn sym(name: &str) -> Term {
    Term::symbol(name)
}

fn tagged_payload<'a>(term: &'a Term, tag: &str) -> &'a Term {
    let object = term.as_object().expect("expected an object");
    object.get(tag).expect("missing expected tag")
}

#[test]
fn eval_returns_symbols_and_literal_objects_as_values() {
    assert_eq!(
        click::eval(&sym(":ok")).expect("eval should succeed"),
        sym(":ok")
    );

    let object: Term = Object::new().with(":x", sym(":y")).into();
    assert_eq!(click::eval(&object).expect("eval should succeed"), object);
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
fn parse_can_express_executable_object_shapes() {
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
fn set_updates_an_object_using_a_computed_key() {
    let env: Term = Object::new().with(":field_name", sym(":answer")).into();
    let expr = click::set(
        Object::new().with(":existing", sym(":present")).into(),
        click::var(":field_name"),
        sym(":value"),
    );
    let expected: Term = Object::new()
        .with(":answer", sym(":value"))
        .with(":existing", sym(":present"))
        .into();

    assert_eq!(
        click::eval_in_env(&expr, &env).expect("eval should succeed"),
        expected
    );
}

#[test]
fn match_dispatches_on_the_unique_overlapping_key() {
    let handlers: Term = Object::new()
        .with(":left", click::lambda(":x", click::var(":x")))
        .with(":right", click::lambda(":y", sym(":wrong")))
        .into();
    let value: Term = Object::new().with(":left", sym(":payload")).into();

    assert_eq!(
        click::eval(&click::r#match(handlers, value)).expect("eval should succeed"),
        sym(":payload")
    );
}

#[test]
fn match_errors_without_a_unique_overlap() {
    let handlers: Term = Object::new()
        .with(":left", click::lambda(":x", click::var(":x")))
        .with(":right", click::lambda(":y", click::var(":y")))
        .into();

    let no_overlap: Term = Object::new().with(":other", sym(":payload")).into();
    assert_eq!(
        click::eval(&click::r#match(handlers.clone(), no_overlap))
            .expect_err("match without overlap should fail"),
        ":match_none"
    );

    let ambiguous: Term = Object::new()
        .with(":left", sym(":a"))
        .with(":right", sym(":b"))
        .into();
    assert_eq!(
        click::eval(&click::r#match(handlers, ambiguous))
            .expect_err("match with two overlaps should fail"),
        ":match_ambiguous"
    );
}

#[test]
fn step_uses_the_explicit_continue_return_error_protocol() {
    let first = click::step(&click::initial_state(sym(":ok"))).expect("step should succeed");
    let next_state = tagged_payload(&first, ":continue").clone();
    let second = click::step(&next_state).expect("step should succeed");

    assert_eq!(tagged_payload(&second, ":return"), &sym(":ok"));

    let error = click::step(&sym(":not_a_state")).expect("step should succeed");
    assert_eq!(tagged_payload(&error, ":error"), &sym(":bad_state"));
}

#[test]
fn applying_a_non_closure_is_an_error() {
    assert_eq!(
        click::eval(&click::apply(sym(":not_a_function"), sym(":arg")))
            .expect_err("applying a bare symbol should fail"),
        ":apply_non_closure"
    );
}

#[test]
fn run_source_ignores_shebang_and_returns_the_last_value() {
    assert_eq!(
        run_source("#!/usr/bin/env click\n(:first :ok)\n(:second :done)\n")
            .expect("run_source should succeed")
            .expect("source should produce a value")
            .to_string(),
        "{:second :done}"
    );
}

#[test]
fn run_source_returns_none_for_empty_input() {
    assert_eq!(run_source("").expect("empty source should parse"), None);
}
