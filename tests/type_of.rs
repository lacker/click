use click::{Fields, Name, NameMap, Symbol, Term, type_of};

#[test]
fn literals_have_builtin_types() {
    assert_eq!(
        type_of(&NameMap::new(), &Term::bool(true)).expect("bool should have a type"),
        Term::bool_type()
    );
    assert_eq!(
        type_of(&NameMap::new(), &Term::nil()).expect("nil should have a type"),
        Term::nil_type()
    );
}

#[test]
fn type_terms_live_in_type() {
    let field_types = Fields::new().with(Symbol::from("flag"), Term::bool_type());

    assert_eq!(
        type_of(&NameMap::new(), &Term::bool_type()).expect("Bool should be a type"),
        Term::r#type()
    );
    assert_eq!(
        type_of(
            &NameMap::new(),
            &Term::arrow(Term::bool_type(), Term::nil_type()),
        )
        .expect("arrow type should be a type"),
        Term::r#type()
    );
    assert_eq!(
        type_of(&NameMap::new(), &Term::record_type(field_types))
            .expect("record type should be a type"),
        Term::r#type()
    );
    assert_eq!(
        type_of(
            &NameMap::new(),
            &Term::sum_type(Fields::new().with(Symbol::from("left"), Term::bool_type())),
        )
        .expect("sum type should be a type"),
        Term::r#type()
    );
}

#[test]
fn variables_and_lambdas_use_the_name_type_map() {
    let x = Name::fresh(Symbol::from("x"));
    let types = NameMap::new().with(x.clone(), Term::bool_type());

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
    let types = NameMap::new().with(x.clone(), Term::bool_type());
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
    let types = NameMap::new().with(x.clone(), Term::bool_type());
    let id = Term::lambda(x.clone(), Term::var(x));

    assert_eq!(
        type_of(&types, &Term::app(id, Term::nil())).expect_err("application should fail"),
        "app argument failed: expected Bool, got Nil"
    );
}

#[test]
fn record_operations_synthesize_record_types() {
    let record = Term::with(
        Term::record(Fields::new()),
        Symbol::from("flag"),
        Term::bool(true),
    );
    let record_type =
        Term::record_type(Fields::new().with(Symbol::from("flag"), Term::bool_type()));

    assert_eq!(
        type_of(&NameMap::new(), &record).expect("record update should typecheck"),
        record_type
    );
    assert_eq!(
        type_of(
            &NameMap::new(),
            &Term::get(record.clone(), Symbol::from("flag"))
        )
        .expect("get should synthesize the field type"),
        Term::bool_type()
    );
    assert_eq!(
        type_of(&NameMap::new(), &Term::has(record, Symbol::from("flag")))
            .expect("has should return Bool"),
        Term::bool_type()
    );
}

#[test]
fn variant_synthesizes_its_explicit_sum_type() {
    let sum_type = Fields::new()
        .with(Symbol::from("left"), Term::bool_type())
        .with(Symbol::from("right"), Term::nil_type());

    assert_eq!(
        type_of(
            &NameMap::new(),
            &Term::variant(Symbol::from("left"), Term::bool(true), sum_type.clone()),
        )
        .expect("variant should synthesize its sum type"),
        Term::sum_type(sum_type)
    );
}

#[test]
fn lambda_requires_a_binder_type_in_the_environment() {
    let x = Name::fresh(Symbol::from("x"));

    assert_eq!(
        type_of(&NameMap::new(), &Term::lambda(x.clone(), Term::var(x)))
            .expect_err("lambda should need a binder type"),
        "missing type for lambda binder 'x'"
    );
}
