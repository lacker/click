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
        ok!("quote builds a list", "(quote (a b c))", "(a b c)"),
        ok!("quote shorthand", "'(a b c)", "(a b c)"),
        ok!("quote returns literal atoms", "'hello", "hello"),
        ok!("quote leaves code shapes as data", "'(var x)", "(var x)"),
        ok!(
            "top level def extends the context for later forms",
            "(def answer 'yes)\n(var answer)",
            "yes"
        ),
        ok!(
            "defs can be used by later definitions",
            "(def outer 'a)\n(def pair (cons (var outer) nil))\n(var pair)",
            "(a)"
        ),
        ok!(
            "defs can hold functions",
            "(def id (lambda x (var x)))\n(app (var id) 'a)",
            "a"
        ),
        ok!(
            "check validates an expected value and keeps processing",
            "(check (app (lambda x (var x)) 'a) 'a)\ntrue",
            "true"
        ),
        ok!(
            "theorem validates an expected value and binds it",
            "(theorem yes_value 'yes 'yes)\n(var yes_value)",
            "yes"
        ),
        ok!(
            "object builds an empty named object",
            "(object)",
            "(object)"
        ),
        ok!(
            "with inserts named values into an object",
            "(with (object) 'foo 'bar)",
            "(object (foo bar))"
        ),
        ok!(
            "with overwrites an existing object key",
            "(with (with (object) 'foo 'old) 'foo 'new)",
            "(object (foo new))"
        ),
        ok!(
            "get reads an inserted object key",
            "(get (with (object) 'foo 'bar) 'foo)",
            "bar"
        ),
        ok!(
            "has reports whether an object key exists",
            "(has (with (object) 'foo 'bar) 'foo)",
            "true"
        ),
        ok!("atom is false for lists", "(atom (quote (a b)))", "false"),
        ok!("atom is false for objects", "(atom (object))", "false"),
        ok!("atom is true for quoted atoms", "(atom 'hello)", "true"),
        ok!(
            "atom_eq matches equal atoms",
            "(atom_eq 'hello 'hello)",
            "true"
        ),
        ok!(
            "atom_eq distinguishes booleans",
            "(atom_eq true false)",
            "false"
        ),
        ok!("car returns the head", "(car '(a b c))", "a"),
        ok!("cdr returns the tail", "(cdr '(a b c))", "(b c)"),
        ok!("cons builds proper lists", "(cons 'a '(b c))", "(a b c)"),
        ok!("cons builds dotted pairs", "(cons 'a 'b)", "(a . b)"),
        ok!("if takes the true branch", "(if true 'yes 'no)", "yes"),
        ok!("if treats nil as falsey", "(if nil 'yes 'no)", "no"),
        ok!("if treats false as falsey", "(if false 'yes 'no)", "no"),
        ok!("if treats atoms as truthy", "(if 'maybe 'yes 'no)", "yes"),
        ok!(
            "lambda produces an internal function value",
            "(lambda x (var x))",
            "#<function>"
        ),
        ok!(
            "app applies a named variable binder",
            "(app (lambda x (var x)) 'a)",
            "a"
        ),
        ok!(
            "app nests explicitly",
            "(app (app (lambda x (lambda y (var x))) 'outer) 'inner)",
            "outer"
        ),
        ok!(
            "substitution preserves outer binders under nested lambdas",
            "(app (app (lambda x (lambda y (cons (var x) (cons (var y) nil)))) 'outer) 'inner)",
            "(outer inner)"
        ),
        ok!(
            "keywords can be used as variable names",
            "(app (lambda if (var if)) 'a)",
            "a"
        ),
        err!(
            "top level var must be bound",
            "(var x)",
            "unbound variable 'x'"
        ),
        err!(
            "app rejects non-functions",
            "(app 'a 'b)",
            "attempted to call a non-function"
        ),
        err!(
            "old implicit application syntax is rejected",
            "((lambda x (var x)) 'a)",
            "form heads must be keyword atoms"
        ),
        err!(
            "lambda binder must be an atom",
            "(lambda '(x) (var x))",
            "lambda binder must be an atom"
        ),
        err!(
            "var name must be an atom",
            "(var '(x))",
            "var name must be an atom"
        ),
        ok!(
            "lambda allows shadowing and resolves the innermost binder",
            "(app (app (lambda x (lambda x (var x))) 'outer) 'inner)",
            "inner"
        ),
        err!(
            "lambda bodies are scope checked eagerly",
            "(lambda x (var y))",
            "unbound variable 'y'"
        ),
        err!(
            "unknown form tags are rejected",
            "(hello 'a)",
            "unknown form 'hello'"
        ),
        err!(
            "nested def is rejected as a term form",
            "(app (lambda x (def y 'a)) 'b)",
            "def is only valid as a top-level declaration"
        ),
        err!(
            "nested check is rejected as a term form",
            "(app (lambda x (check 'a 'a)) 'b)",
            "check is only valid as a top-level declaration"
        ),
        err!(
            "nested theorem is rejected as a term form",
            "(app (lambda x (theorem y 'a 'a)) 'b)",
            "theorem is only valid as a top-level declaration"
        ),
        err!(
            "duplicate top level defs are rejected",
            "(def x 'a)\n(def x 'b)",
            "definition 'x' is already declared"
        ),
        err!(
            "check fails when values differ",
            "(check 'a 'b)",
            "check failed: expected b, got a"
        ),
        err!(
            "theorem fails when values differ",
            "(theorem x 'a 'b)",
            "theorem failed: expected b, got a"
        ),
        err!(
            "get rejects missing object keys",
            "(get (object) 'foo)",
            "missing object key 'foo'"
        ),
        err!(
            "get rejects non-object inputs",
            "(get 'foo 'bar)",
            "get object must be an object"
        ),
        err!(
            "with requires symbol keys",
            "(with (object) true 'bar)",
            "with key must be a symbol"
        ),
        err!(
            "car nil is undefined",
            "(car nil)",
            "car expects a non-empty list"
        ),
        err!(
            "cdr nil is undefined",
            "(cdr nil)",
            "cdr expects a non-empty list"
        ),
        ok!(
            "shebang line is ignored",
            "#!/usr/bin/env click\n(cons 'a '(b c))\n",
            "(a b c)"
        ),
        ok!(
            "multiple top level forms return the last value",
            "true\n(cons 'a nil)\n",
            "(a)"
        ),
        err!(
            "atom_eq rejects list arguments",
            "(atom_eq '(a) '(a))",
            "atom_eq expects atom arguments"
        ),
        err!(
            "cons rejects unquoted atoms",
            "(cons a '(b c))",
            "unbound atom 'a'"
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
