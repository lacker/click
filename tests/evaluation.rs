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
            "(def answer (record))\n(var answer)",
            "(record)"
        ),
        ok!(
            "defs can be used by later definitions",
            "(def flag (variant left (record) (sum-type (left (record-type)) (right (record-type)))))\n(def answer (match (var flag) (left (lambda x (record))) (right (lambda y (record (other (record)))))))\n(var answer)",
            "(record)"
        ),
        ok!(
            "defs can hold functions",
            "(def id (lambda x (var x)))\n(app (var id) (record))",
            "(record)"
        ),
        ok!(
            "check validates an expected value and keeps processing",
            "(check (app (lambda x (var x)) (record)) (record))\n(record)",
            "(record)"
        ),
        ok!(
            "theorem validates an expected value and binds it",
            "(theorem truth (record) (record))\n(var truth)",
            "(record)"
        ),
        ok!(
            "record builds an empty named record",
            "(record)",
            "(record)"
        ),
        ok!(
            "record can be built directly from fields",
            "(record (foo (record)))",
            "(record (foo (record)))"
        ),
        ok!(
            "get reads an inserted record key",
            "(get (record (foo (record))) foo)",
            "(record)"
        ),
        ok!(
            "lambda produces an internal function value",
            "(lambda x (var x))",
            "#<function>"
        ),
        ok!("Type evaluates to itself", "Type", "Type"),
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
            "arrow syntax lowers to canonical pi types",
            "(arrow (record-type) (record-type))",
            "(pi _ (record-type) (record-type))"
        ),
        ok!(
            "pi types evaluate to themselves",
            "(pi x Type (var x))",
            "(pi x Type (var x))"
        ),
        ok!(
            "variants evaluate to themselves",
            "(variant left (record) (sum-type (left (record-type)) (right (record-type))))",
            "(variant left (record) (sum-type (left (record-type)) (right (record-type))))"
        ),
        ok!(
            "match selects the matching variant handler",
            "(match (variant left (record) (sum-type (left (record-type)) (right (record-type)))) (left (lambda x (var x))) (right (lambda y (record (other (record))))))",
            "(record)"
        ),
        ok!(
            "app applies a named variable binder",
            "(app (lambda x (var x)) (record))",
            "(record)"
        ),
        ok!(
            "app nests explicitly",
            "(app (app (lambda x (lambda y (var x))) (record)) (record (other (record))))",
            "(record)"
        ),
        ok!(
            "substitution preserves outer binders under nested lambdas",
            "(get (app (app (lambda x (lambda y (record (left (var x))))) (record)) (record (other (record)))) left)",
            "(record)"
        ),
        ok!(
            "keywords can be used as variable names",
            "(app (lambda if (var if)) (record))",
            "(record)"
        ),
        err!(
            "top level var must be bound",
            "(var x)",
            "unbound variable 'x'"
        ),
        err!(
            "app rejects non-functions",
            "(app (record) (record))",
            "attempted to call a non-function"
        ),
        err!(
            "old implicit application syntax is rejected",
            "((lambda x (var x)) (record))",
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
            "(app (app (lambda x (lambda x (var x))) (record)) (record (other (record))))",
            "(record (other (record)))"
        ),
        err!(
            "lambda bodies are scope checked eagerly",
            "(lambda x (var y))",
            "unbound variable 'y'"
        ),
        err!(
            "unknown form tags are rejected",
            "(hello (record))",
            "unknown form 'hello'"
        ),
        err!(
            "nested def is rejected as a term form",
            "(app (lambda x (def y (record))) (record))",
            "def is only valid as a top-level declaration"
        ),
        err!(
            "nested check is rejected as a term form",
            "(app (lambda x (check (record) (record))) (record))",
            "check is only valid as a top-level declaration"
        ),
        err!(
            "nested theorem is rejected as a term form",
            "(app (lambda x (theorem y (record) (record))) (record))",
            "theorem is only valid as a top-level declaration"
        ),
        err!(
            "duplicate top level defs are rejected",
            "(def x (record))\n(def x (record (other (record))))",
            "definition 'x' is already declared"
        ),
        err!(
            "check fails when values differ",
            "(check (record) (record (other (record))))",
            "check failed: expected (record (other (record))), got (record)"
        ),
        err!(
            "theorem fails when values differ",
            "(theorem x (record) (record (other (record))))",
            "theorem failed: expected (record (other (record))), got (record)"
        ),
        err!(
            "get rejects missing record keys",
            "(get (record) foo)",
            "missing record key 'foo'"
        ),
        err!(
            "get rejects non-record inputs",
            "(get Type foo)",
            "get record must be a record"
        ),
        err!(
            "match rejects non-variant scrutinees",
            "(match (record) (left (lambda x (var x))))",
            "match scrutinee must be a variant, got (record)"
        ),
        err!(
            "if is no longer supported",
            "(if (record) (record) (record))",
            "if is no longer supported in the kernel"
        ),
        err!(
            "match rejects missing handlers for the chosen tag",
            "(match (variant left (record) (sum-type (left (record-type)) (right (record-type)))) (right (lambda y (record))))",
            "missing match handler 'left'"
        ),
        ok!(
            "shebang line is ignored",
            "#!/usr/bin/env click\n(record (answer (record)))\n",
            "(record (answer (record)))"
        ),
        ok!(
            "multiple top level forms return the last value",
            "Type\n(record)\n",
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
