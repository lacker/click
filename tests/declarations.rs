use click::{Context, Declaration, Symbol, Term, declare};

#[test]
fn declare_extends_the_context_purely() {
    let context = Context::new();
    let context = declare(
        &context,
        Declaration::Def {
            name: Symbol::from("answer"),
            value: Term::bool(true),
        },
    )
    .expect("declaration should succeed");

    assert_eq!(context.get("answer"), Some(&Term::bool(true)));
    assert_eq!(Context::new().get("answer"), None);
}

#[test]
fn check_leaves_the_context_unchanged() {
    let context = declare(
        &Context::new(),
        Declaration::Def {
            name: Symbol::from("answer"),
            value: Term::bool(true),
        },
    )
    .expect("definition should succeed");

    let checked = declare(
        &context,
        Declaration::Check {
            actual: Term::global(Symbol::from("answer")),
            expected: Term::bool(true),
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
            actual: Term::bool(true),
            expected: Term::bool(true),
        },
    )
    .expect("theorem should succeed");

    assert_eq!(context.get("answer_value"), Some(&Term::bool(true)));
}
