use click::{Context, Declaration, Name, Symbol, SymbolMap, Term, declare};

#[test]
fn lambda_uses_names_for_binders_and_variables() {
    let x = Name::fresh(Symbol::from("x"));
    let id_name = Name::fresh(Symbol::from("id"));
    let id = Term::lambda(x.clone(), Term::var(x));

    let context = declare(
        &Context::new(),
        Declaration::Def {
            name: id_name.clone(),
            value: id,
        },
    )
    .expect("definition should succeed");

    declare(
        &context,
        Declaration::Check {
            actual: Term::app(Term::var(id_name), Term::record(SymbolMap::new())),
            expected: Term::record(SymbolMap::new()),
        },
    )
    .expect("identity should apply");
}

#[test]
fn nested_lambdas_preserve_outer_names() {
    let x = Name::fresh(Symbol::from("x"));
    let y = Name::fresh(Symbol::from("y"));
    let fst_name = Name::fresh(Symbol::from("fst"));
    let fst = Term::lambda(x.clone(), Term::lambda(y, Term::var(x)));

    let context = declare(
        &Context::new(),
        Declaration::Def {
            name: fst_name.clone(),
            value: fst,
        },
    )
    .expect("definition should succeed");

    declare(
        &context,
        Declaration::Check {
            actual: Term::app(
                Term::app(Term::var(fst_name), Term::record(SymbolMap::new())),
                Term::record(SymbolMap::new()),
            ),
            expected: Term::record(SymbolMap::new()),
        },
    )
    .expect("outer binder should remain visible beneath the inner lambda");
}

#[test]
fn inner_lambda_shadows_the_outer_name() {
    let outer = Name::fresh(Symbol::from("x"));
    let inner = Name::fresh(Symbol::from("x"));
    let shadow_name = Name::fresh(Symbol::from("shadow"));
    let shadow = Term::lambda(outer, Term::lambda(inner.clone(), Term::var(inner)));

    let context = declare(
        &Context::new(),
        Declaration::Def {
            name: shadow_name.clone(),
            value: shadow,
        },
    )
    .expect("definition should succeed");

    declare(
        &context,
        Declaration::Check {
            actual: Term::app(
                Term::app(Term::var(shadow_name), Term::record(SymbolMap::new())),
                Term::record(SymbolMap::new()),
            ),
            expected: Term::record(SymbolMap::new()),
        },
    )
    .expect("inner binder should shadow the outer binder");
}
