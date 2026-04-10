use click::{Branches, Fields, Name, NameMap, Symbol, Term, type_of};

#[test]
fn literals_have_builtin_types() {
    assert_eq!(
        type_of(&NameMap::new(), &Term::nil()).expect("nil should have a type"),
        Term::nil_type()
    );
}

#[test]
fn type_terms_live_in_type() {
    let field_types = Fields::new().with(Symbol::from("flag"), Term::nil_type());

    assert_eq!(
        type_of(
            &NameMap::new(),
            &Term::arrow(Term::nil_type(), Term::nil_type()),
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
            &Term::sum_type(Fields::new().with(Symbol::from("left"), Term::nil_type())),
        )
        .expect("sum type should be a type"),
        Term::r#type()
    );
}

#[test]
fn variables_and_lambdas_use_the_name_type_map() {
    let x = Name::fresh(Symbol::from("x"));
    let types = NameMap::new().with(x.clone(), Term::nil_type());

    assert_eq!(
        type_of(&types, &Term::var(x.clone())).expect("variable should typecheck"),
        Term::nil_type()
    );
    assert_eq!(
        type_of(&types, &Term::lambda(x.clone(), Term::var(x)))
            .expect("lambda should synthesize a function type"),
        Term::arrow(Term::nil_type(), Term::nil_type())
    );
}

#[test]
fn application_of_identity_returns_the_result_type() {
    let x = Name::fresh(Symbol::from("x"));
    let types = NameMap::new().with(x.clone(), Term::nil_type());
    let id = Term::lambda(x.clone(), Term::var(x));

    assert_eq!(
        type_of(&types, &Term::app(id, Term::nil()))
            .expect("well-typed application should synthesize a result type"),
        Term::nil_type()
    );
}

#[test]
fn application_rejects_a_mismatched_argument_type() {
    let x = Name::fresh(Symbol::from("x"));
    let types = NameMap::new().with(x.clone(), Term::nil_type());
    let id = Term::lambda(x.clone(), Term::var(x));

    assert_eq!(
        type_of(&types, &Term::app(id, Term::record(Fields::new())))
            .expect_err("application should fail"),
        "app argument failed: expected Nil, got (record-type)"
    );
}

#[test]
fn record_literals_and_get_synthesize_record_types() {
    let record = Term::record(Fields::new().with(Symbol::from("flag"), Term::nil()));
    let record_type = Term::record_type(Fields::new().with(Symbol::from("flag"), Term::nil_type()));

    assert_eq!(
        type_of(&NameMap::new(), &record).expect("record literal should typecheck"),
        record_type
    );
    assert_eq!(
        type_of(
            &NameMap::new(),
            &Term::get(record.clone(), Symbol::from("flag"))
        )
        .expect("get should synthesize the field type"),
        Term::nil_type()
    );
}

#[test]
fn variant_synthesizes_its_explicit_sum_type() {
    let sum_type = Fields::new()
        .with(Symbol::from("left"), Term::nil_type())
        .with(Symbol::from("right"), Term::nil_type());

    assert_eq!(
        type_of(
            &NameMap::new(),
            &Term::variant(Symbol::from("left"), Term::nil(), sum_type.clone()),
        )
        .expect("variant should synthesize its sum type"),
        Term::sum_type(sum_type)
    );
}

#[test]
fn case_synthesizes_the_common_branch_result_type() {
    let left = Name::fresh(Symbol::from("left_value"));
    let right = Name::fresh(Symbol::from("right_value"));
    let sum_type = Fields::new()
        .with(Symbol::from("left"), Term::nil_type())
        .with(Symbol::from("right"), Term::nil_type());

    let term = Term::case(
        Term::variant(Symbol::from("left"), Term::nil(), sum_type),
        Branches::new()
            .with(Symbol::from("left"), left.clone(), Term::var(left))
            .with(Symbol::from("right"), right, Term::nil()),
    );

    assert_eq!(
        type_of(&NameMap::new(), &term).expect("case should synthesize a branch result type"),
        Term::nil_type()
    );
}

#[test]
fn case_rejects_mismatched_branch_result_types() {
    let left = Name::fresh(Symbol::from("left_value"));
    let right = Name::fresh(Symbol::from("right_value"));
    let sum_type = Fields::new()
        .with(Symbol::from("left"), Term::nil_type())
        .with(Symbol::from("right"), Term::nil_type());

    let term = Term::case(
        Term::variant(Symbol::from("left"), Term::nil(), sum_type),
        Branches::new()
            .with(Symbol::from("left"), left, Term::nil())
            .with(
                Symbol::from("right"),
                right.clone(),
                Term::record(Fields::new()),
            ),
    );

    assert_eq!(
        type_of(&NameMap::new(), &term).expect_err("case should require matching branch types"),
        "case branches failed: expected Nil, got (record-type)"
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
