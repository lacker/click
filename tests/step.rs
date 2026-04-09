use click::{Context, Declaration, StepResult, Symbol, Term, declare, step};

#[test]
fn public_step_reports_values() {
    match step(&Context::new(), &Term::bool(true)).expect("step should succeed") {
        StepResult::Value(value) => assert_eq!(value, Term::bool(true)),
        StepResult::Reduced(next) => panic!("expected a value, got reduct {next}"),
    }
}

#[test]
fn public_step_reduces_a_global_reference_using_the_context() {
    let context = declare(
        &Context::new(),
        Declaration::Def {
            name: Symbol::from("answer"),
            value: Term::bool(true),
        },
    )
    .expect("definition should succeed");

    match step(&context, &Term::var(Symbol::from("answer"))).expect("step should succeed") {
        StepResult::Reduced(next) => assert_eq!(next, Term::bool(true)),
        StepResult::Value(value) => panic!("expected a reduct, got value {value}"),
    }
}

#[test]
fn public_step_performs_one_beta_reduction() {
    let term = Term::app(
        Term::lambda(
            Symbol::from("x"),
            Term::app(
                Term::lambda(Symbol::from("y"), Term::var(Symbol::from("y"))),
                Term::var(Symbol::from("x")),
            ),
        ),
        Term::bool(true),
    );

    match step(&Context::new(), &term).expect("step should succeed") {
        StepResult::Reduced(next) => assert_eq!(next.to_string(), "(app #<function> true)"),
        StepResult::Value(value) => panic!("expected a reduct, got value {value}"),
    }
}
