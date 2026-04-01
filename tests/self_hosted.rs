use click::run_source;

const FIX: &str = r#"
(lambda f
  (app
    (lambda x1
      (app
        (var f)
        (lambda y1
          (app
            (app (var x1) (var x1))
            (var y1)))))
    (lambda x2
      (app
        (var f)
        (lambda y2
          (app
            (app (var x2) (var x2))
            (var y2)))))))
"#;

fn eval(source: &str) -> String {
    run_source(source)
        .expect("program should succeed")
        .expect("program should produce a value")
        .to_string()
}

fn if_expr(
    cond: impl AsRef<str>,
    then_expr: impl AsRef<str>,
    else_expr: impl AsRef<str>,
) -> String {
    format!(
        "(if {} {} {})",
        cond.as_ref(),
        then_expr.as_ref(),
        else_expr.as_ref()
    )
}

fn cons_expr(head: impl AsRef<str>, tail: impl AsRef<str>) -> String {
    format!("(cons {} {})", head.as_ref(), tail.as_ref())
}

fn app_expr(function: impl AsRef<str>, arg: impl AsRef<str>) -> String {
    format!("(app {} {})", function.as_ref(), arg.as_ref())
}

fn var_expr(name: &str) -> String {
    format!("(var {name})")
}

fn request(tag: &str, first: impl AsRef<str>, second: impl AsRef<str>) -> String {
    cons_expr(
        format!("'{tag}"),
        cons_expr(first, cons_expr(second, "nil")),
    )
}

fn self_call(arg: impl AsRef<str>) -> String {
    app_expr(var_expr("recur"), arg)
}

fn exact_arity_2(term: &str, success: impl AsRef<str>) -> String {
    if_expr(
        format!("(atom (cdr {term}))"),
        "false",
        if_expr(
            format!("(atom (cdr (cdr {term})))"),
            if_expr(
                format!("(atom_eq (cdr (cdr {term})) nil)"),
                success,
                "false",
            ),
            "false",
        ),
    )
}

fn exact_arity_3(term: &str, success: impl AsRef<str>) -> String {
    if_expr(
        format!("(atom (cdr {term}))"),
        "false",
        if_expr(
            format!("(atom (cdr (cdr {term})))"),
            "false",
            if_expr(
                format!("(atom (cdr (cdr (cdr {term}))))"),
                if_expr(
                    format!("(atom_eq (cdr (cdr (cdr {term}))) nil)"),
                    success,
                    "false",
                ),
                "false",
            ),
        ),
    )
}

fn exact_arity_4(term: &str, success: impl AsRef<str>) -> String {
    if_expr(
        format!("(atom (cdr {term}))"),
        "false",
        if_expr(
            format!("(atom (cdr (cdr {term})))"),
            "false",
            if_expr(
                format!("(atom (cdr (cdr (cdr {term}))))"),
                "false",
                if_expr(
                    format!("(atom (cdr (cdr (cdr (cdr {term})))))"),
                    if_expr(
                        format!("(atom_eq (cdr (cdr (cdr (cdr {term})))) nil)"),
                        success,
                        "false",
                    ),
                    "false",
                ),
            ),
        ),
    )
}

fn named_core_worker() -> String {
    let req = var_expr("req");
    let tag = format!("(car {req})");

    let contains_name = format!("(car (cdr {req}))");
    let contains_ctx = format!("(car (cdr (cdr {req})))");
    let contains_case = if_expr(
        format!("(atom {contains_ctx})"),
        "false",
        if_expr(
            format!("(atom_eq (car {contains_ctx}) {contains_name})"),
            "true",
            self_call(request(
                "contains",
                &contains_name,
                format!("(cdr {contains_ctx})"),
            )),
        ),
    );

    let term = format!("(car (cdr {req}))");
    let ctx = format!("(car (cdr (cdr {req})))");
    let head = format!("(car {term})");

    let quoted_case = exact_arity_2(&term, "true");

    let var_name = format!("(car (cdr {term}))");
    let var_case = exact_arity_2(
        &term,
        if_expr(
            format!("(atom {var_name})"),
            self_call(request("contains", &var_name, &ctx)),
            "false",
        ),
    );

    let app_fn = format!("(car (cdr {term}))");
    let app_arg = format!("(car (cdr (cdr {term})))");
    let app_case = exact_arity_3(
        &term,
        if_expr(
            self_call(request("wf", &app_fn, &ctx)),
            self_call(request("wf", &app_arg, &ctx)),
            "false",
        ),
    );

    let binder = format!("(car (cdr {term}))");
    let body = format!("(car (cdr (cdr {term})))");
    let extended_ctx = format!("(cons {binder} {ctx})");
    let lambda_case = exact_arity_3(
        &term,
        if_expr(
            format!("(atom {binder})"),
            if_expr(
                self_call(request("contains", &binder, &ctx)),
                "false",
                self_call(request("wf", &body, &extended_ctx)),
            ),
            "false",
        ),
    );

    let wf_non_atom = if_expr(
        format!("(atom {head})"),
        if_expr(
            format!("(atom_eq {head} 'quote)"),
            &quoted_case,
            if_expr(
                format!("(atom_eq {head} 'var)"),
                &var_case,
                if_expr(
                    format!("(atom_eq {head} 'app)"),
                    &app_case,
                    if_expr(format!("(atom_eq {head} 'lambda)"), &lambda_case, "false"),
                ),
            ),
        ),
        "false",
    );

    let wf_atom = if_expr(
        format!("(atom_eq {term} nil)"),
        "true",
        if_expr(
            format!("(atom_eq {term} true)"),
            "true",
            format!("(atom_eq {term} false)"),
        ),
    );

    let wf_case = if_expr(format!("(atom {term})"), wf_atom, wf_non_atom);

    let top = if_expr(
        format!("(atom {req})"),
        "false",
        if_expr(
            format!("(atom {tag})"),
            if_expr(
                format!("(atom_eq {tag} 'contains)"),
                contains_case,
                if_expr(format!("(atom_eq {tag} 'wf)"), wf_case, "false"),
            ),
            "false",
        ),
    );

    format!("(lambda recur (lambda req {top}))")
}

fn token_core_worker() -> String {
    let req = var_expr("req");
    let tag = format!("(car {req})");

    let contains_token = format!("(car (cdr {req}))");
    let contains_ctx = format!("(car (cdr (cdr {req})))");
    let contains_case = if_expr(
        format!("(atom {contains_ctx})"),
        "false",
        if_expr(
            format!("(atom_eq (car {contains_ctx}) {contains_token})"),
            "true",
            self_call(request(
                "contains",
                &contains_token,
                format!("(cdr {contains_ctx})"),
            )),
        ),
    );

    let term = format!("(car (cdr {req}))");
    let ctx = format!("(car (cdr (cdr {req})))");
    let head = format!("(car {term})");

    let var_token = format!("(car (cdr {term}))");
    let var_case = exact_arity_2(
        &term,
        if_expr(
            format!("(atom {var_token})"),
            self_call(request("contains", &var_token, &ctx)),
            "false",
        ),
    );

    let app_fn = format!("(car (cdr {term}))");
    let app_arg = format!("(car (cdr (cdr {term})))");
    let app_case = exact_arity_3(
        &term,
        if_expr(
            self_call(request("wf", &app_fn, &ctx)),
            self_call(request("wf", &app_arg, &ctx)),
            "false",
        ),
    );

    let binder = format!("(car (cdr {term}))");
    let domain = format!("(car (cdr (cdr {term})))");
    let body = format!("(car (cdr (cdr (cdr {term}))))");
    let extended_ctx = format!("(cons {binder} {ctx})");

    let lambda_case = exact_arity_4(
        &term,
        if_expr(
            format!("(atom {binder})"),
            if_expr(
                self_call(request("contains", &binder, &ctx)),
                "false",
                if_expr(
                    self_call(request("wf", &domain, &ctx)),
                    self_call(request("wf", &body, &extended_ctx)),
                    "false",
                ),
            ),
            "false",
        ),
    );

    let pi_case = exact_arity_4(
        &term,
        if_expr(
            format!("(atom {binder})"),
            if_expr(
                self_call(request("contains", &binder, &ctx)),
                "false",
                if_expr(
                    self_call(request("wf", &domain, &ctx)),
                    self_call(request("wf", &body, &extended_ctx)),
                    "false",
                ),
            ),
            "false",
        ),
    );

    let wf_non_atom = if_expr(
        format!("(atom {head})"),
        if_expr(
            format!("(atom_eq {head} 'var)"),
            &var_case,
            if_expr(
                format!("(atom_eq {head} 'app)"),
                &app_case,
                if_expr(
                    format!("(atom_eq {head} 'lambda)"),
                    &lambda_case,
                    if_expr(format!("(atom_eq {head} 'pi)"), &pi_case, "false"),
                ),
            ),
        ),
        "false",
    );

    let wf_case = if_expr(
        format!("(atom {term})"),
        format!("(atom_eq {term} 'type)"),
        wf_non_atom,
    );

    let top = if_expr(
        format!("(atom {req})"),
        "false",
        if_expr(
            format!("(atom {tag})"),
            if_expr(
                format!("(atom_eq {tag} 'contains)"),
                contains_case,
                if_expr(format!("(atom_eq {tag} 'wf)"), wf_case, "false"),
            ),
            "false",
        ),
    );

    format!("(lambda recur (lambda req {top}))")
}

fn run_recursive_checker(worker: &str, term: &str) -> String {
    let checker = app_expr(FIX, worker);
    let request = request("wf", term, "nil");
    eval(&app_expr(checker, request))
}

fn run_named_core_checker(term: &str) -> String {
    run_recursive_checker(&named_core_worker(), term)
}

fn run_token_core_checker(term: &str) -> String {
    run_recursive_checker(&token_core_worker(), term)
}

#[test]
fn named_core_checker_accepts_small_terms() {
    assert_eq!(run_named_core_checker("nil"), "true");
    assert_eq!(run_named_core_checker("true"), "true");
    assert_eq!(run_named_core_checker("(quote (quote hello))"), "true");
    assert_eq!(run_named_core_checker("(quote (quote (a b)))"), "true");
    assert_eq!(run_named_core_checker("(quote (lambda x (var x)))"), "true");
    assert_eq!(
        run_named_core_checker("(quote (app (lambda x (var x)) (quote a)))"),
        "true"
    );
}

#[test]
fn named_core_checker_rejects_bad_scoping_and_shapes() {
    assert_eq!(run_named_core_checker("(quote hello)"), "false");
    assert_eq!(run_named_core_checker("(quote (quote))"), "false");
    assert_eq!(run_named_core_checker("(quote (var x))"), "false");
    assert_eq!(
        run_named_core_checker("(quote (lambda x (lambda x (var x))))"),
        "false"
    );
    assert_eq!(run_named_core_checker("(quote (lambda x))"), "false");
    assert_eq!(
        run_named_core_checker("(quote (app (lambda x (var x))))"),
        "false"
    );
}

#[test]
fn token_core_checker_accepts_closed_terms() {
    assert_eq!(run_token_core_checker("(quote type)"), "true");
    assert_eq!(
        run_token_core_checker("(quote (lambda x type (var x)))"),
        "true"
    );
    assert_eq!(run_token_core_checker("(quote (pi x type type))"), "true");
    assert_eq!(
        run_token_core_checker("(quote (app (lambda x type (var x)) type))"),
        "true"
    );
}

#[test]
fn token_core_checker_rejects_bad_scoping_and_bad_shapes() {
    assert_eq!(run_token_core_checker("(quote (var x))"), "false");
    assert_eq!(
        run_token_core_checker("(quote (lambda x type (var y)))"),
        "false"
    );
    assert_eq!(
        run_token_core_checker("(quote (lambda x type (lambda x type (var x))))"),
        "false"
    );
    assert_eq!(run_token_core_checker("(quote (lambda x type))"), "false");
    assert_eq!(
        run_token_core_checker("(quote (app (lambda x type (var x))))"),
        "false"
    );
}
