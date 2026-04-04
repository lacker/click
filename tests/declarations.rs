use click::{Context, Declaration, SExpr, Value, declare};

#[test]
fn declare_extends_the_context_purely() {
    let context = Context::new();
    let context = declare(
        &context,
        Declaration::Def {
            name: "answer".to_string(),
            value: SExpr::Symbol("true".to_string()),
        },
    )
    .expect("declaration should succeed");

    assert_eq!(context.get("answer"), Some(&Value::Bool(true)));
    assert_eq!(Context::new().get("answer"), None);
}

#[test]
fn check_leaves_the_context_unchanged() {
    let context = declare(
        &Context::new(),
        Declaration::Def {
            name: "answer".to_string(),
            value: SExpr::Symbol("true".to_string()),
        },
    )
    .expect("definition should succeed");

    let checked = declare(
        &context,
        Declaration::Check {
            actual: SExpr::List(vec![
                SExpr::Symbol("var".to_string()),
                SExpr::Symbol("answer".to_string()),
            ]),
            expected: SExpr::Symbol("true".to_string()),
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
            name: "yes_value".to_string(),
            actual: SExpr::List(vec![
                SExpr::Symbol("quote".to_string()),
                SExpr::Symbol("yes".to_string()),
            ]),
            expected: SExpr::List(vec![
                SExpr::Symbol("quote".to_string()),
                SExpr::Symbol("yes".to_string()),
            ]),
        },
    )
    .expect("theorem should succeed");

    assert_eq!(
        context.get("yes_value"),
        Some(&Value::Atom("yes".to_string()))
    );
}
