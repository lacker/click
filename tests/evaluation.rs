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
            "object builds an empty named object",
            "(object)",
            "(object)"
        ),
        ok!(
            "with inserts named values into an object",
            "(with (object) foo true)",
            "(object (foo true))"
        ),
        ok!(
            "with overwrites an existing object key",
            "(with (with (object) foo false) foo true)",
            "(object (foo true))"
        ),
        ok!(
            "get reads an inserted object key",
            "(get (with (object) foo true) foo)",
            "true"
        ),
        ok!(
            "has reports whether an object key exists",
            "(has (with (object) foo true) foo)",
            "true"
        ),
        ok!("if takes the true branch", "(if true false nil)", "false"),
        ok!("if treats nil as falsey", "(if nil true false)", "false"),
        ok!("if treats false as falsey", "(if false true nil)", "nil"),
        ok!(
            "if treats objects as truthy",
            "(if (object) true false)",
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
            "arrow types evaluate to themselves",
            "(arrow Bool Nil)",
            "(arrow Bool Nil)"
        ),
        ok!(
            "object types evaluate to themselves",
            "(object-type)",
            "(object-type)"
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
            "(get (app (app (lambda x (lambda y (with (object) left (var x)))) true) false) left)",
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
            "get rejects missing object keys",
            "(get (object) foo)",
            "missing object key 'foo'"
        ),
        err!(
            "get rejects non-object inputs",
            "(get true foo)",
            "get object must be an object"
        ),
        err!(
            "with requires symbol keys",
            "(with (object) (object) true)",
            "with key must be an atom"
        ),
        ok!(
            "shebang line is ignored",
            "#!/usr/bin/env click\n(with (object) answer true)\n",
            "(object (answer true))"
        ),
        ok!(
            "multiple top level forms return the last value",
            "true\n(object)\n",
            "(object)"
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
