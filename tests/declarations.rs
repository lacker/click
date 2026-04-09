use click::{Context, Declaration, Symbol, Term, declare};

#[test]
fn declare_extends_the_context_purely() {
    let context = Context::new();
    let context = declare(
        &context,
        Declaration::Def {
            name: Symbol::from("answer"),
            value: Term::Bool(true),
        },
    )
    .expect("declaration should succeed");

    assert_eq!(context.get("answer"), Some(&Term::Bool(true)));
    assert_eq!(Context::new().get("answer"), None);
}

#[test]
fn check_leaves_the_context_unchanged() {
    let context = declare(
        &Context::new(),
        Declaration::Def {
            name: Symbol::from("answer"),
            value: Term::Bool(true),
        },
    )
    .expect("definition should succeed");

    let checked = declare(
        &context,
        Declaration::Check {
            actual: Term::Global(Symbol::from("answer")),
            expected: Term::Bool(true),
        },
    )
    .expect("check should succeed");

    assert_eq!(checked, context);
}

#[test]
fn theorem_checks_and_binds_a_name() {
    let context = declare(
        &Context::new(),
        Declaration::Theorem {
            name: Symbol::from("answer_value"),
            actual: Term::Bool(true),
            expected: Term::Bool(true),
        },
    )
    .expect("theorem should succeed");

    assert_eq!(context.get("answer_value"), Some(&Term::Bool(true)));
}
