use click::run_source;

#[derive(Clone, Copy)]
struct EvalCase {
    name: &'static str,
    expr: &'static str,
    expected: Expected,
}

#[derive(Clone, Copy)]
enum Expected {
    Value(&'static str),
    Error(&'static str),
}

macro_rules! ok {
    ($name:expr, $expr:expr, $expected:expr) => {
        EvalCase {
            name: $name,
            expr: $expr,
            expected: Expected::Value($expected),
        }
    };
}

macro_rules! err {
    ($name:expr, $expr:expr, $expected:expr) => {
        EvalCase {
            name: $name,
            expr: $expr,
            expected: Expected::Error($expected),
        }
    };
}

#[test]
fn evaluation_cases() {
    let cases = [
        err!(
            "bare atoms do not self evaluate",
            "hello",
            "unbound atom 'hello'"
        ),
        ok!(
            "top level def extends the context for later forms",
            "(def answer nil)\n(var answer)",
            "nil"
        ),
        ok!(
            "defs can be used by later definitions",
            "(def flag (variant left nil (sum-type (left Nil) (right Nil))))\n(def answer (case (var flag) (left x nil) (right y (record))))\n(var answer)",
            "nil"
        ),
        ok!(
            "defs can hold functions",
            "(def id (lambda x (var x)))\n(app (var id) nil)",
            "nil"
        ),
        ok!(
            "check validates an expected value and keeps processing",
            "(check (app (lambda x (var x)) nil) nil)\n(record)",
            "(record)"
        ),
        ok!(
            "theorem validates an expected value and binds it",
            "(theorem truth nil nil)\n(var truth)",
            "nil"
        ),
        ok!(
            "record builds an empty named record",
            "(record)",
            "(record)"
        ),
        ok!(
            "record can be built directly from fields",
            "(record (foo nil))",
            "(record (foo nil))"
        ),
        ok!(
            "get reads an inserted record key",
            "(get (record (foo nil)) foo)",
            "nil"
        ),
        ok!(
            "lambda produces an internal function value",
            "(lambda x (var x))",
            "#<function>"
        ),
        ok!("Type evaluates to itself", "Type", "Type"),
        ok!("Nil evaluates to itself", "Nil", "Nil"),
        ok!(
            "record types evaluate to themselves",
            "(record-type)",
            "(record-type)"
        ),
        ok!(
            "sum types evaluate to themselves",
            "(sum-type)",
            "(sum-type)"
        ),
        ok!(
            "arrow types evaluate to themselves",
            "(arrow Nil Nil)",
            "(arrow Nil Nil)"
        ),
        ok!(
            "variants evaluate to themselves",
            "(variant left nil (sum-type (left Nil) (right Nil)))",
            "(variant left nil (sum-type (left Nil) (right Nil)))"
        ),
        ok!(
            "case selects the matching variant branch",
            "(case (variant left nil (sum-type (left Nil) (right Nil))) (left x (var x)) (right y (record)))",
            "nil"
        ),
        ok!(
            "app applies a named variable binder",
            "(app (lambda x (var x)) nil)",
            "nil"
        ),
        ok!(
            "app nests explicitly",
            "(app (app (lambda x (lambda y (var x))) nil) (record))",
            "nil"
        ),
        ok!(
            "substitution preserves outer binders under nested lambdas",
            "(get (app (app (lambda x (lambda y (record (left (var x))))) nil) (record)) left)",
            "nil"
        ),
        ok!(
            "keywords can be used as variable names",
            "(app (lambda if (var if)) nil)",
            "nil"
        ),
        err!(
            "top level var must be bound",
            "(var x)",
            "unbound variable 'x'"
        ),
        err!(
            "app rejects non-functions",
            "(app nil (record))",
            "attempted to call a non-function"
        ),
        err!(
            "old implicit application syntax is rejected",
            "((lambda x (var x)) nil)",
            "form heads must be keyword atoms"
        ),
        err!(
            "lambda binder must be an atom",
            "(lambda (x) (var x))",
            "lambda binder must be an atom"
        ),
        err!(
            "var name must be an atom",
            "(var (x))",
            "var name must be an atom"
        ),
        ok!(
            "lambda allows shadowing and resolves the innermost binder",
            "(app (app (lambda x (lambda x (var x))) nil) (record))",
            "(record)"
        ),
        err!(
            "lambda bodies are scope checked eagerly",
            "(lambda x (var y))",
            "unbound variable 'y'"
        ),
        err!(
            "unknown form tags are rejected",
            "(hello nil)",
            "unknown form 'hello'"
        ),
        err!(
            "nested def is rejected as a term form",
            "(app (lambda x (def y nil)) (record))",
            "def is only valid as a top-level declaration"
        ),
        err!(
            "nested check is rejected as a term form",
            "(app (lambda x (check nil nil)) (record))",
            "check is only valid as a top-level declaration"
        ),
        err!(
            "nested theorem is rejected as a term form",
            "(app (lambda x (theorem y nil nil)) (record))",
            "theorem is only valid as a top-level declaration"
        ),
        err!(
            "duplicate top level defs are rejected",
            "(def x nil)\n(def x (record))",
            "definition 'x' is already declared"
        ),
        err!(
            "check fails when values differ",
            "(check nil (record))",
            "check failed: expected (record), got nil"
        ),
        err!(
            "theorem fails when values differ",
            "(theorem x nil (record))",
            "theorem failed: expected (record), got nil"
        ),
        err!(
            "get rejects missing record keys",
            "(get (record) foo)",
            "missing record key 'foo'"
        ),
        err!(
            "get rejects non-record inputs",
            "(get nil foo)",
            "get record must be a record"
        ),
        err!(
            "case rejects non-variant scrutinees",
            "(case nil (left x (var x)))",
            "case scrutinee must be a variant, got nil"
        ),
        err!(
            "if is no longer supported",
            "(if nil nil nil)",
            "if is no longer supported in the kernel"
        ),
        err!(
            "case rejects missing branches for the chosen tag",
            "(case (variant left nil (sum-type (left Nil) (right Nil))) (right y (record)))",
            "missing case branch 'left'"
        ),
        ok!(
            "shebang line is ignored",
            "#!/usr/bin/env click\n(record (answer nil))\n",
            "(record (answer nil))"
        ),
        ok!(
            "multiple top level forms return the last value",
            "nil\n(record)\n",
            "(record)"
        ),
    ];

    let mut failures = Vec::new();

    for case in cases {
        match case.expected {
            Expected::Value(expected) => match run_source(case.expr) {
                Ok(Some(actual)) => {
                    let actual = actual.to_string();
                    if actual != expected {
                        failures.push(format!(
                            "{}\nexpression: {}\nexpected: {}\nactual: {}",
                            case.name, case.expr, expected, actual
                        ));
                    }
                }
                Ok(None) => failures.push(format!(
                    "{}\nexpression: {}\nexpected: {}\nactual: <no value>",
                    case.name, case.expr, expected
                )),
                Err(error) => failures.push(format!(
                    "{}\nexpression: {}\nexpected: {}\nerror: {}",
                    case.name, case.expr, expected, error
                )),
            },
            Expected::Error(expected) => match run_source(case.expr) {
                Ok(Some(actual)) => failures.push(format!(
                    "{}\nexpression: {}\nexpected error containing: {}\nactual value: {}",
                    case.name, case.expr, expected, actual
                )),
                Ok(None) => failures.push(format!(
                    "{}\nexpression: {}\nexpected error containing: {}\nactual: <no value>",
                    case.name, case.expr, expected
                )),
                Err(error) => {
                    if !error.contains(expected) {
                        failures.push(format!(
                            "{}\nexpression: {}\nexpected error containing: {}\nactual error: {}",
                            case.name, case.expr, expected, error
                        ));
                    }
                }
            },
        }
    }

    assert!(
        failures.is_empty(),
        "evaluation failures:\n\n{}",
        failures.join("\n\n")
    );
}
