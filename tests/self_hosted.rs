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

fn eval(source: &str) -> String {
    run_source(source)
        .expect("program should succeed")
        .expect("program should produce a value")
        .to_string()
}

fn run_checker(term: &str) -> String {
    eval(&format!("({CLOSURE_SHAPE_CHECKER} {term})"))
}

#[test]
fn closure_shape_checker_accepts_runtime_closures() {
    assert_eq!(run_checker("(lambda stack)"), "true");
}

#[test]
fn closure_shape_checker_accepts_well_shaped_quoted_closures() {
    assert_eq!(run_checker("(quote (closure stack nil))"), "true");
}

#[test]
fn closure_shape_checker_rejects_non_closures() {
    assert_eq!(run_checker("(quote hello)"), "false");
    assert_eq!(run_checker("(quote (closure stack))"), "false");
    assert_eq!(run_checker("(quote (closure stack nil extra))"), "false");
}
