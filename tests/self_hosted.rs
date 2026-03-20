use click::run_source;

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
