use click::{Context, Declaration, Symbol, Term, declare};

#[test]
fn smart_lambda_binds_a_named_occurrence() {
    let x = Symbol::from("x");
    let id = Term::lambda(x.clone(), Term::var(x));

    let context = declare(
        &Context::new(),
        Declaration::Def {
            name: Symbol::from("id"),
            value: id,
        },
    )
    .expect("definition should succeed");

    declare(
        &context,
        Declaration::Check {
            actual: Term::app(Term::var(Symbol::from("id")), Term::bool(true)),
            expected: Term::bool(true),
        },
    )
    .expect("identity should apply");
}

#[test]
fn smart_lambda_threads_outer_binders_under_nested_lambdas() {
    let x = Symbol::from("x");
    let y = Symbol::from("y");
    let fst = Term::lambda(x.clone(), Term::lambda(y, Term::var(x)));

    let context = declare(
        &Context::new(),
        Declaration::Def {
            name: Symbol::from("fst"),
            value: fst,
        },
    )
    .expect("definition should succeed");

    declare(
        &context,
        Declaration::Check {
            actual: Term::app(
                Term::app(Term::var(Symbol::from("fst")), Term::bool(true)),
                Term::bool(false),
            ),
            expected: Term::bool(true),
        },
    )
    .expect("outer binder should remain visible beneath the inner lambda");
}

#[test]
fn smart_lambda_respects_shadowing_by_name() {
    let x = Symbol::from("x");
    let shadow = Term::lambda(x.clone(), Term::lambda(x, Term::var(Symbol::from("x"))));

    let context = declare(
        &Context::new(),
        Declaration::Def {
            name: Symbol::from("shadow"),
            value: shadow,
        },
    )
    .expect("definition should succeed");

    declare(
        &context,
        Declaration::Check {
            actual: Term::app(
                Term::app(Term::var(Symbol::from("shadow")), Term::bool(true)),
                Term::bool(false),
            ),
            expected: Term::bool(false),
        },
    )
    .expect("inner binder should shadow the outer binder");
}
