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
            "(def answer true)\n(var answer)",
            "true"
        ),
        ok!(
            "defs can be used by later definitions",
            "(def flag true)\n(def answer (if (var flag) false true))\n(var answer)",
            "false"
        ),
        ok!(
            "defs can hold functions",
            "(def id (lambda x (var x)))\n(app (var id) true)",
            "true"
        ),
        ok!(
            "check validates an expected value and keeps processing",
            "(check (app (lambda x (var x)) true) true)\nfalse",
            "false"
        ),
        ok!(
            "theorem validates an expected value and binds it",
            "(theorem truth true true)\n(var truth)",
            "true"
        ),
        ok!(
            "record builds an empty named record",
            "(record)",
            "(record)"
        ),
        ok!(
            "record can be built directly from fields",
            "(record (foo true))",
            "(record (foo true))"
        ),
        ok!(
            "with inserts named values into a record",
            "(with (record) foo true)",
            "(record (foo true))"
        ),
        ok!(
            "with overwrites an existing record key",
            "(with (with (record) foo false) foo true)",
            "(record (foo true))"
        ),
        ok!(
            "get reads an inserted record key",
            "(get (with (record) foo true) foo)",
            "true"
        ),
        ok!(
            "has reports whether a record key exists",
            "(has (with (record) foo true) foo)",
            "true"
        ),
        ok!("if takes the true branch", "(if true false nil)", "false"),
        ok!("if treats nil as falsey", "(if nil true false)", "false"),
        ok!("if treats false as falsey", "(if false true nil)", "nil"),
        ok!(
            "if treats records as truthy",
            "(if (record) true false)",
            "true"
        ),
        ok!(
            "lambda produces an internal function value",
            "(lambda x (var x))",
            "#<function>"
        ),
        ok!("Type evaluates to itself", "Type", "Type"),
        ok!("Bool evaluates to itself", "Bool", "Bool"),
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
            "(arrow Bool Nil)",
            "(arrow Bool Nil)"
        ),
        ok!(
            "variants evaluate to themselves",
            "(variant left true (sum-type (left Bool) (right Nil)))",
            "(variant left true (sum-type (left Bool) (right Nil)))"
        ),
        ok!(
            "app applies a named variable binder",
            "(app (lambda x (var x)) true)",
            "true"
        ),
        ok!(
            "app nests explicitly",
            "(app (app (lambda x (lambda y (var x))) true) false)",
            "true"
        ),
        ok!(
            "substitution preserves outer binders under nested lambdas",
            "(get (app (app (lambda x (lambda y (with (record) left (var x)))) true) false) left)",
            "true"
        ),
        ok!(
            "keywords can be used as variable names",
            "(app (lambda if (var if)) true)",
            "true"
        ),
        err!(
            "top level var must be bound",
            "(var x)",
            "unbound variable 'x'"
        ),
        err!(
            "app rejects non-functions",
            "(app true false)",
            "attempted to call a non-function"
        ),
        err!(
            "old implicit application syntax is rejected",
            "((lambda x (var x)) true)",
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
            "(app (app (lambda x (lambda x (var x))) true) false)",
            "false"
        ),
        err!(
            "lambda bodies are scope checked eagerly",
            "(lambda x (var y))",
            "unbound variable 'y'"
        ),
        err!(
            "unknown form tags are rejected",
            "(hello true)",
            "unknown form 'hello'"
        ),
        err!(
            "nested def is rejected as a term form",
            "(app (lambda x (def y true)) false)",
            "def is only valid as a top-level declaration"
        ),
        err!(
            "nested check is rejected as a term form",
            "(app (lambda x (check true true)) false)",
            "check is only valid as a top-level declaration"
        ),
        err!(
            "nested theorem is rejected as a term form",
            "(app (lambda x (theorem y true true)) false)",
            "theorem is only valid as a top-level declaration"
        ),
        err!(
            "duplicate top level defs are rejected",
            "(def x true)\n(def x false)",
            "definition 'x' is already declared"
        ),
        err!(
            "check fails when values differ",
            "(check true false)",
            "check failed: expected false, got true"
        ),
        err!(
            "theorem fails when values differ",
            "(theorem x true false)",
            "theorem failed: expected false, got true"
        ),
        err!(
            "get rejects missing record keys",
            "(get (record) foo)",
            "missing record key 'foo'"
        ),
        err!(
            "get rejects non-record inputs",
            "(get true foo)",
            "get record must be a record"
        ),
        err!(
            "with requires symbol keys",
            "(with (record) (record) true)",
            "with key must be an atom"
        ),
        ok!(
            "shebang line is ignored",
            "#!/usr/bin/env click\n(with (record) answer true)\n",
            "(record (answer true))"
        ),
        ok!(
            "multiple top level forms return the last value",
            "true\n(record)\n",
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
