use click::run_source;

const FIX: &str = r#"
(lambda
  ((lambda
     ((car (cdr stack))
      (lambda
        (((car (cdr stack)) (car (cdr stack)))
         (car stack)))))
   (lambda
     ((car (cdr stack))
      (lambda
        (((car (cdr stack)) (car (cdr stack)))
         (car stack)))))))
"#;

const CLOSURE_SHAPE_CHECKER: &str = r#"
(lambda
  (if (atom (car stack))
      false
      (if (atom (car (car stack)))
          (if (atom_eq (car (car stack)) 'closure)
              (if (atom (cdr (car stack)))
                  false
                  (if (atom (cdr (cdr (car stack))))
                      false
                      (if (atom (cdr (cdr (cdr (car stack)))))
                          (atom_eq (cdr (cdr (cdr (car stack)))) nil)
                          false)))
              false)
          false)))
"#;

const TINY_CORE_WELL_FORMEDNESS_CHECKER: &str = r#"
(
  (lambda
    ((lambda
       ((car (cdr stack))
        (lambda
          (((car (cdr stack)) (car (cdr stack)))
           (car stack)))))
     (lambda
       ((car (cdr stack))
        (lambda
          (((car (cdr stack)) (car (cdr stack)))
           (car stack)))))))
  (lambda
    (lambda
      (if (atom (car stack))
          (if (atom_eq (car stack) nil)
              true
              (if (atom_eq (car stack) true)
                  true
                  (if (atom_eq (car stack) false)
                      true
                      (atom_eq (car stack) 'stack))))
          (if (atom (car (car stack)))
              (if (atom_eq (car (car stack)) 'quote)
                  (if (atom (cdr (car stack)))
                      false
                      (if (atom (cdr (cdr (car stack))))
                          (atom_eq (cdr (cdr (car stack))) nil)
                          false))
                  (if (atom_eq (car (car stack)) 'lambda)
                      (if (atom (cdr (car stack)))
                          false
                          (if (atom (cdr (cdr (car stack))))
                              (if (atom_eq (cdr (cdr (car stack))) nil)
                                  ((car (cdr stack)) (car (cdr (car stack))))
                                  false)
                              false))
                      (if (atom (cdr (car stack)))
                          false
                          (if (atom (cdr (cdr (car stack))))
                              (if (atom_eq (cdr (cdr (car stack))) nil)
                                  (if ((car (cdr stack)) (car (car stack)))
                                      ((car (cdr stack)) (car (cdr (car stack))))
                                      false)
                                  false)
                              false))))
              (if (atom (cdr (car stack)))
                  false
                  (if (atom (cdr (cdr (car stack))))
                      (if (atom_eq (cdr (cdr (car stack))) nil)
                          (if ((car (cdr stack)) (car (car stack)))
                              ((car (cdr stack)) (car (cdr (car stack))))
                              false)
                          false)
                      false)))))))
"#;

fn eval(source: &str) -> String {
    run_source(source)
        .expect("program should succeed")
        .expect("program should produce a value")
        .to_string()
}

fn run_checker(checker: &str, term: &str) -> String {
    eval(&format!("({checker} {term})"))
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

fn request(tag: &str, first: impl AsRef<str>, second: impl AsRef<str>) -> String {
    cons_expr(
        format!("'{tag}"),
        cons_expr(first, cons_expr(second, "nil")),
    )
}

fn self_call(arg: impl AsRef<str>) -> String {
    format!("((car (cdr stack)) {})", arg.as_ref())
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

fn token_core_worker() -> String {
    let req = "(car stack)";
    let tag = "(car (car stack))";

    let contains_token = "(car (cdr (car stack)))";
    let contains_ctx = "(car (cdr (cdr (car stack))))";
    let contains_case = if_expr(
        format!("(atom {contains_ctx})"),
        "false",
        if_expr(
            format!("(atom_eq (car {contains_ctx}) {contains_token})"),
            "true",
            self_call(request(
                "contains",
                contains_token,
                format!("(cdr {contains_ctx})"),
            )),
        ),
    );

    let term = "(car (cdr (car stack)))";
    let ctx = "(car (cdr (cdr (car stack))))";
    let head = format!("(car {term})");

    let var_token = format!("(car (cdr {term}))");
    let var_case = exact_arity_2(
        term,
        if_expr(
            format!("(atom {var_token})"),
            self_call(request("contains", &var_token, ctx)),
            "false",
        ),
    );

    let app_fn = format!("(car (cdr {term}))");
    let app_arg = format!("(car (cdr (cdr {term})))");
    let app_case = exact_arity_3(
        term,
        if_expr(
            self_call(request("wf", &app_fn, ctx)),
            self_call(request("wf", &app_arg, ctx)),
            "false",
        ),
    );

    let binder = format!("(car (cdr {term}))");
    let domain = format!("(car (cdr (cdr {term})))");
    let body = format!("(car (cdr (cdr (cdr {term}))))");
    let extended_ctx = format!("(cons {binder} {ctx})");

    let lam_case = exact_arity_4(
        term,
        if_expr(
            format!("(atom {binder})"),
            if_expr(
                self_call(request("contains", &binder, ctx)),
                "false",
                if_expr(
                    self_call(request("wf", &domain, ctx)),
                    self_call(request("wf", &body, &extended_ctx)),
                    "false",
                ),
            ),
            "false",
        ),
    );

    let pi_case = exact_arity_4(
        term,
        if_expr(
            format!("(atom {binder})"),
            if_expr(
                self_call(request("contains", &binder, ctx)),
                "false",
                if_expr(
                    self_call(request("wf", &domain, ctx)),
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
                    &lam_case,
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

    format!("(lambda\n  (lambda\n    {top}\n  ))")
}

fn run_token_core_checker(term: &str) -> String {
    let worker = token_core_worker();
    eval(&format!(
        "((lambda (({FIX} {worker}) (cons 'wf (cons (car stack) (cons nil nil))))) {term})"
    ))
}

#[test]
fn closure_shape_checker_accepts_runtime_closures() {
    assert_eq!(run_checker(CLOSURE_SHAPE_CHECKER, "(lambda stack)"), "true");
}

#[test]
fn closure_shape_checker_accepts_well_shaped_quoted_closures() {
    assert_eq!(
        run_checker(CLOSURE_SHAPE_CHECKER, "(quote (closure stack nil))"),
        "true"
    );
}

#[test]
fn closure_shape_checker_rejects_non_closures() {
    assert_eq!(run_checker(CLOSURE_SHAPE_CHECKER, "(quote hello)"), "false");
    assert_eq!(
        run_checker(CLOSURE_SHAPE_CHECKER, "(quote (closure stack))"),
        "false"
    );
    assert_eq!(
        run_checker(CLOSURE_SHAPE_CHECKER, "(quote (closure stack nil extra))"),
        "false"
    );
}

#[test]
fn tiny_core_well_formedness_checker_accepts_small_terms() {
    assert_eq!(
        run_checker(TINY_CORE_WELL_FORMEDNESS_CHECKER, "(quote stack)"),
        "true"
    );
    assert_eq!(
        run_checker(TINY_CORE_WELL_FORMEDNESS_CHECKER, "(quote (quote hello))"),
        "true"
    );
    assert_eq!(
        run_checker(TINY_CORE_WELL_FORMEDNESS_CHECKER, "(quote (lambda stack))"),
        "true"
    );
    assert_eq!(
        run_checker(
            TINY_CORE_WELL_FORMEDNESS_CHECKER,
            "(quote ((lambda stack) (quote a)))",
        ),
        "true"
    );
    assert_eq!(
        run_checker(
            TINY_CORE_WELL_FORMEDNESS_CHECKER,
            "(quote (((lambda stack) (quote a)) (quote b)))",
        ),
        "true"
    );
}

#[test]
fn tiny_core_well_formedness_checker_rejects_outside_the_fragment() {
    assert_eq!(
        run_checker(TINY_CORE_WELL_FORMEDNESS_CHECKER, "(quote hello)"),
        "false"
    );
    assert_eq!(
        run_checker(TINY_CORE_WELL_FORMEDNESS_CHECKER, "(quote (quote))"),
        "false"
    );
    assert_eq!(
        run_checker(TINY_CORE_WELL_FORMEDNESS_CHECKER, "(quote (lambda))"),
        "false"
    );
    assert_eq!(
        run_checker(
            TINY_CORE_WELL_FORMEDNESS_CHECKER,
            "(quote (lambda stack stack))",
        ),
        "false"
    );
    assert_eq!(
        run_checker(
            TINY_CORE_WELL_FORMEDNESS_CHECKER,
            "(quote (if true nil nil))"
        ),
        "false"
    );
    assert_eq!(
        run_checker(
            TINY_CORE_WELL_FORMEDNESS_CHECKER,
            "(quote ((lambda stack) hello))",
        ),
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
