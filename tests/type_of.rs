use click::{Name, Object, Symbol, Term, TypeMap, type_of};

#[test]
fn literals_have_builtin_types() {
    assert_eq!(
        type_of(&TypeMap::new(), &Term::bool(true)).expect("bool should have a type"),
        Term::bool_type()
    );
    assert_eq!(
        type_of(&TypeMap::new(), &Term::nil()).expect("nil should have a type"),
        Term::nil_type()
    );
}

#[test]
fn type_terms_live_in_type() {
    let field_types = Object::new().with(Symbol::from("flag"), Term::bool_type());

    assert_eq!(
        type_of(&TypeMap::new(), &Term::bool_type()).expect("Bool should be a type"),
        Term::r#type()
    );
    assert_eq!(
        type_of(
            &TypeMap::new(),
            &Term::arrow(Term::bool_type(), Term::nil_type()),
        )
        .expect("arrow type should be a type"),
        Term::r#type()
    );
    assert_eq!(
        type_of(&TypeMap::new(), &Term::object_type(field_types))
            .expect("object type should be a type"),
        Term::r#type()
    );
}

#[test]
fn variables_and_lambdas_use_the_name_type_map() {
    let x = Name::fresh(Symbol::from("x"));
    let types = TypeMap::new().with(x.clone(), Term::bool_type());

    assert_eq!(
        type_of(&types, &Term::var(x.clone())).expect("variable should typecheck"),
        Term::bool_type()
    );
    assert_eq!(
        type_of(&types, &Term::lambda(x.clone(), Term::var(x)))
            .expect("lambda should synthesize a function type"),
        Term::arrow(Term::bool_type(), Term::bool_type())
    );
}

#[test]
fn application_of_identity_returns_the_result_type() {
    let x = Name::fresh(Symbol::from("x"));
    let types = TypeMap::new().with(x.clone(), Term::bool_type());
    let id = Term::lambda(x.clone(), Term::var(x));

    assert_eq!(
        type_of(&types, &Term::app(id, Term::bool(true)))
            .expect("well-typed application should synthesize a result type"),
        Term::bool_type()
    );
}

#[test]
fn application_rejects_a_mismatched_argument_type() {
    let x = Name::fresh(Symbol::from("x"));
    let types = TypeMap::new().with(x.clone(), Term::bool_type());
    let id = Term::lambda(x.clone(), Term::var(x));

    assert_eq!(
        type_of(&types, &Term::app(id, Term::nil())).expect_err("application should fail"),
        "app argument failed: expected Bool, got Nil"
    );
}

#[test]
fn object_operations_synthesize_record_types() {
    let object = Term::with(
        Term::object(Object::new()),
        Symbol::from("flag"),
        Term::bool(true),
    );
    let object_type =
        Term::object_type(Object::new().with(Symbol::from("flag"), Term::bool_type()));

    assert_eq!(
        type_of(&TypeMap::new(), &object).expect("object update should typecheck"),
        object_type
    );
    assert_eq!(
        type_of(
            &TypeMap::new(),
            &Term::get(object.clone(), Symbol::from("flag"))
        )
        .expect("get should synthesize the field type"),
        Term::bool_type()
    );
    assert_eq!(
        type_of(&TypeMap::new(), &Term::has(object, Symbol::from("flag")))
            .expect("has should return Bool"),
        Term::bool_type()
    );
}

#[test]
fn lambda_requires_a_binder_type_in_the_environment() {
    let x = Name::fresh(Symbol::from("x"));

    assert_eq!(
        type_of(&TypeMap::new(), &Term::lambda(x.clone(), Term::var(x)))
            .expect_err("lambda should need a binder type"),
        "missing type for lambda binder 'x'"
    );
}
