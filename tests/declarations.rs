use click::{Context, Declaration, Expr, Value, declare};

#[test]
fn declare_extends_the_context_purely() {
    let context = Context::new();
    let context = declare(
        &context,
        Declaration::Def {
            name: "answer".to_string(),
            value: Expr::Symbol("true".to_string()),
        },
    )
    .expect("declaration should succeed");

    assert_eq!(context.get("answer"), Some(&Value::Bool(true)));
    assert_eq!(Context::new().get("answer"), None);
}
