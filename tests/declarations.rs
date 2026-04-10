use click::{Context, Declaration, Name, Symbol, Term, declare};

#[test]
fn declare_extends_the_context_purely() {
    let answer = Name::fresh(Symbol::from("answer"));
    let context = Context::new();
    let context = declare(
        &context,
        Declaration::Def {
            name: answer.clone(),
            value: Term::nil(),
        },
    )
    .expect("declaration should succeed");

    assert_eq!(context.get(&answer), Some(&Term::nil()));
    assert_eq!(Context::new().get(&answer), None);
}

#[test]
fn check_leaves_the_context_unchanged() {
    let answer = Name::fresh(Symbol::from("answer"));
    let context = declare(
        &Context::new(),
        Declaration::Def {
            name: answer.clone(),
            value: Term::nil(),
        },
    )
    .expect("definition should succeed");

    let checked = declare(
        &context,
        Declaration::Check {
            actual: Term::var(answer),
            expected: Term::nil(),
        },
    )
    .expect("check should succeed");

    assert_eq!(checked, context);
}

#[test]
fn theorem_checks_and_binds_a_name() {
    let answer_value = Name::fresh(Symbol::from("answer_value"));
    let context = declare(
        &Context::new(),
        Declaration::Theorem {
            name: answer_value.clone(),
            actual: Term::nil(),
            expected: Term::nil(),
        },
    )
    .expect("theorem should succeed");

    assert_eq!(context.get(&answer_value), Some(&Term::nil()));
}
