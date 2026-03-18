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
    // Add new evaluation checks here. Each row is just expression text plus
    // the rendered value, or an expected error substring.
    let cases = [
        err!(
            "bare atoms do not self evaluate",
            "hello",
            "unbound atom 'hello'"
        ),
        ok!("stack is empty at top level", "stack", "nil"),
        ok!("quote builds a list", "(quote (a b c))", "(a b c)"),
        ok!("quote shorthand", "'(a b c)", "(a b c)"),
        ok!("quote returns literal atoms", "'hello", "hello"),
        ok!("quote leaves stack as data", "'stack", "stack"),
        ok!("atom is false for lists", "(atom (quote (a b)))", "false"),
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
        ok!("lambda returns closures", "(lambda stack)", "#<closure>"),
        ok!(
            "calling lambda pushes onto stack",
            "((lambda stack) 'a)",
            "(a)"
        ),
        ok!(
            "car stack reads the nearest bound value",
            "((lambda (car stack)) 'a)",
            "a"
        ),
        ok!(
            "cdr stack reaches outer bindings",
            "(((lambda (lambda (car (cdr stack)))) 'a) 'b)",
            "a"
        ),
        ok!(
            "lambda captures lexical environment",
            "(((lambda (lambda (car (cdr stack)))) 'outer) 'inner)",
            "outer"
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
        err!(
            "top-level stack is empty",
            "(car stack)",
            "car expects a non-empty list"
        ),
        err!(
            "calling a non-function is an error",
            "('a 'b)",
            "attempted to call a non-function"
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
