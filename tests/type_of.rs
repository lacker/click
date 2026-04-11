use click::{Name, NameMap, Symbol, SymbolMap, Term, type_of};

#[test]
fn literals_have_builtin_types() {
    assert_eq!(
        type_of(&NameMap::new(), &Term::record(SymbolMap::new()))
            .expect("record should have a type"),
        Term::record_type(SymbolMap::new())
    );
}

#[test]
fn type_terms_live_in_type() {
    let field_types =
        SymbolMap::new().with(Symbol::from("flag"), Term::record_type(SymbolMap::new()));
    let x = Name::fresh(Symbol::from("x"));

    assert_eq!(
        type_of(
            &NameMap::new(),
            &Term::arrow(
                Term::record_type(SymbolMap::new()),
                Term::record_type(SymbolMap::new()),
            ),
        )
        .expect("arrow type should be a type"),
        Term::r#type()
    );
    assert_eq!(
        type_of(
            &NameMap::new(),
            &Term::pi(x.clone(), Term::r#type(), Term::r#type()),
        )
        .expect("pi type should be a type"),
        Term::r#type()
    );
    assert_eq!(
        type_of(
            &NameMap::new(),
            &Term::pi(x.clone(), Term::r#type(), Term::var(x)),
        )
        .expect("dependent pi type should be a type"),
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
            &Term::sum_type(
                SymbolMap::new().with(Symbol::from("left"), Term::record_type(SymbolMap::new())),
            ),
        )
        .expect("sum type should be a type"),
        Term::r#type()
    );
}

#[test]
fn variables_and_lambdas_use_the_name_type_map() {
    let x = Name::fresh(Symbol::from("x"));
    let types = NameMap::new().with(x.clone(), Term::record_type(SymbolMap::new()));

    assert_eq!(
        type_of(&types, &Term::var(x.clone())).expect("variable should typecheck"),
        Term::record_type(SymbolMap::new())
    );
    assert_eq!(
        type_of(&types, &Term::lambda(x.clone(), Term::var(x)))
            .expect("lambda should synthesize a function type"),
        Term::arrow(
            Term::record_type(SymbolMap::new()),
            Term::record_type(SymbolMap::new()),
        )
    );
}

#[test]
fn application_of_identity_returns_the_result_type() {
    let x = Name::fresh(Symbol::from("x"));
    let types = NameMap::new().with(x.clone(), Term::record_type(SymbolMap::new()));
    let id = Term::lambda(x.clone(), Term::var(x));

    assert_eq!(
        type_of(&types, &Term::app(id, Term::record(SymbolMap::new())))
            .expect("well-typed application should synthesize a result type"),
        Term::record_type(SymbolMap::new())
    );
}

#[test]
fn dependent_application_substitutes_the_argument_into_the_result_type() {
    let x = Name::fresh(Symbol::from("x"));
    let f = Name::fresh(Symbol::from("f"));
    let types = NameMap::new().with(f.clone(), Term::pi(x.clone(), Term::r#type(), Term::var(x)));

    assert_eq!(
        type_of(
            &types,
            &Term::app(Term::var(f), Term::record_type(SymbolMap::new()))
        )
        .expect("dependent application should substitute the argument"),
        Term::record_type(SymbolMap::new())
    );
}

#[test]
fn application_rejects_a_mismatched_argument_type() {
    let x = Name::fresh(Symbol::from("x"));
    let types = NameMap::new().with(x.clone(), Term::record_type(SymbolMap::new()));
    let id = Term::lambda(x.clone(), Term::var(x));

    assert_eq!(
        type_of(&types, &Term::app(id, Term::sum_type(SymbolMap::new())))
            .expect_err("application should fail"),
        "app argument failed: expected (record-type), got Type"
    );
}

#[test]
fn record_literals_and_get_synthesize_record_types() {
    let record =
        Term::record(SymbolMap::new().with(Symbol::from("flag"), Term::record(SymbolMap::new())));
    let record_type = Term::record_type(
        SymbolMap::new().with(Symbol::from("flag"), Term::record_type(SymbolMap::new())),
    );

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
        Term::record_type(SymbolMap::new())
    );
}

#[test]
fn variant_synthesizes_its_explicit_sum_type() {
    let sum_type = SymbolMap::new()
        .with(Symbol::from("left"), Term::record_type(SymbolMap::new()))
        .with(Symbol::from("right"), Term::record_type(SymbolMap::new()));

    assert_eq!(
        type_of(
            &NameMap::new(),
            &Term::variant(
                Symbol::from("left"),
                Term::record(SymbolMap::new()),
                sum_type.clone()
            ),
        )
        .expect("variant should synthesize its sum type"),
        Term::sum_type(sum_type)
    );
}

#[test]
fn match_synthesizes_the_common_handler_result_type() {
    let left = Name::fresh(Symbol::from("left_value"));
    let right = Name::fresh(Symbol::from("right_value"));
    let sum_type = SymbolMap::new()
        .with(Symbol::from("left"), Term::record_type(SymbolMap::new()))
        .with(Symbol::from("right"), Term::record_type(SymbolMap::new()));

    let term = Term::r#match(
        Term::variant(
            Symbol::from("left"),
            Term::record(SymbolMap::new()),
            sum_type,
        ),
        SymbolMap::new()
            .with(
                Symbol::from("left"),
                Term::lambda(left.clone(), Term::var(left)),
            )
            .with(
                Symbol::from("right"),
                Term::lambda(right, Term::record(SymbolMap::new())),
            ),
    );

    assert_eq!(
        type_of(&NameMap::new(), &term).expect("match should synthesize a handler result type"),
        Term::record_type(SymbolMap::new())
    );
}

#[test]
fn match_rejects_mismatched_handler_result_types() {
    let left = Name::fresh(Symbol::from("left_value"));
    let right = Name::fresh(Symbol::from("right_value"));
    let sum_type = SymbolMap::new()
        .with(Symbol::from("left"), Term::record_type(SymbolMap::new()))
        .with(Symbol::from("right"), Term::record_type(SymbolMap::new()));

    let term = Term::r#match(
        Term::variant(
            Symbol::from("left"),
            Term::record(SymbolMap::new()),
            sum_type,
        ),
        SymbolMap::new()
            .with(
                Symbol::from("left"),
                Term::lambda(left, Term::record(SymbolMap::new())),
            )
            .with(
                Symbol::from("right"),
                Term::lambda(right.clone(), Term::sum_type(SymbolMap::new())),
            ),
    );

    assert_eq!(
        type_of(&NameMap::new(), &term).expect_err("match should require matching handler types"),
        "match handlers failed: expected (record-type), got Type"
    );
}

#[test]
fn match_rejects_handler_result_types_that_depend_on_the_payload() {
    let payload = Name::fresh(Symbol::from("payload"));
    let witness = Name::fresh(Symbol::from("witness"));
    let sum_type = SymbolMap::new().with(Symbol::from("left"), Term::r#type());
    let term = Term::r#match(
        Term::variant(
            Symbol::from("left"),
            Term::record_type(SymbolMap::new()),
            sum_type,
        ),
        SymbolMap::new().with(
            Symbol::from("left"),
            Term::lambda(payload.clone(), Term::var(witness.clone())),
        ),
    );
    let types = NameMap::new().with(witness, Term::var(payload));

    assert_eq!(
        type_of(&types, &term).expect_err("match should remain non-dependent"),
        "match handler 'left' result type cannot depend on its argument"
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

#[test]
fn lambda_synthesizes_a_pi_type_when_the_body_type_depends_on_the_binder() {
    let x = Name::fresh(Symbol::from("x"));
    let witness = Name::fresh(Symbol::from("witness"));
    let types = NameMap::new()
        .with(x.clone(), Term::r#type())
        .with(witness.clone(), Term::var(x.clone()));

    assert_eq!(
        type_of(&types, &Term::lambda(x.clone(), Term::var(witness)))
            .expect("lambda should synthesize a dependent pi"),
        Term::pi(x.clone(), Term::r#type(), Term::var(x))
    );
}
