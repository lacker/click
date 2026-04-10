use click::{
    Branches, Context, Declaration, Fields, Name, NameMap, StepResult, Symbol, Term, declare, step,
};

#[test]
fn public_step_reports_values() {
    match step(&NameMap::new(), &Term::record(Fields::new())).expect("step should succeed") {
        StepResult::Value(value) => assert_eq!(value, Term::record(Fields::new())),
        StepResult::Reduced(next) => panic!("expected a value, got reduct {next}"),
    }
}

#[test]
fn public_step_reduces_a_global_reference_using_the_context() {
    let answer = Name::fresh(Symbol::from("answer"));
    let context = declare(
        &Context::new(),
        Declaration::Def {
            name: answer.clone(),
            value: Term::record(Fields::new()),
        },
    )
    .expect("definition should succeed");

    match step(context.values(), &Term::var(answer)).expect("step should succeed") {
        StepResult::Reduced(next) => assert_eq!(next, Term::record(Fields::new())),
        StepResult::Value(value) => panic!("expected a reduct, got value {value}"),
    }
}

#[test]
fn public_step_performs_one_beta_reduction() {
    let x = Name::fresh(Symbol::from("x"));
    let y = Name::fresh(Symbol::from("y"));
    let term = Term::app(
        Term::lambda(
            x.clone(),
            Term::app(Term::lambda(y.clone(), Term::var(y)), Term::var(x)),
        ),
        Term::record(Fields::new()),
    );

    match step(&NameMap::new(), &term).expect("step should succeed") {
        StepResult::Reduced(next) => assert_eq!(next.to_string(), "(app #<function> (record))"),
        StepResult::Value(value) => panic!("expected a reduct, got value {value}"),
    }
}

#[test]
fn public_step_selects_the_matching_case_branch() {
    let left = Name::fresh(Symbol::from("left_value"));
    let right = Name::fresh(Symbol::from("right_value"));
    let term = Term::case(
        Term::variant(
            Symbol::from("left"),
            Term::record(Fields::new()),
            Fields::new()
                .with(Symbol::from("left"), Term::record_type(Fields::new()))
                .with(Symbol::from("right"), Term::record_type(Fields::new())),
        ),
        Branches::new()
            .with(Symbol::from("left"), left.clone(), Term::var(left))
            .with(Symbol::from("right"), right, Term::record(Fields::new())),
    );

    match step(&NameMap::new(), &term).expect("step should succeed") {
        StepResult::Reduced(next) => assert_eq!(next, Term::record(Fields::new())),
        StepResult::Value(value) => panic!("expected a reduct, got value {value}"),
    }
}
