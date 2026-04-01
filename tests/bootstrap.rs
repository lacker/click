use std::fs;
use std::path::{Path, PathBuf};

use click::run_source;

// These tests keep the substantive Click programs in `bootstrap/` and use Rust
// only as a harness: load the files, apply concrete inputs, and compare the
// rendered results.

fn repo_path(relative: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(relative)
}

fn load(relative: &str) -> String {
    fs::read_to_string(repo_path(relative)).expect("bootstrap file should be readable")
}

fn eval(source: &str) -> String {
    run_source(source)
        .expect("program should succeed")
        .expect("program should produce a value")
        .to_string()
}

fn app_expr(function: impl AsRef<str>, arg: impl AsRef<str>) -> String {
    format!("(app {} {})", function.as_ref(), arg.as_ref())
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

// Both well-formedness checkers use the same protocol:
// `(tag term ctx)`, encoded as a simple list request. The worker itself lives in
// Click; Rust just supplies the fixed-point combinator and the top-level request.
fn run_recursive_checker(worker_path: &str, term: &str) -> String {
    let fix = load("bootstrap/base/fix.cl");
    let worker = load(worker_path);
    let checker = app_expr(&fix, &worker);
    let request = request("wf", term, "nil");
    eval(&app_expr(checker, request))
}

fn run_named_core_checker(term: &str) -> String {
    run_recursive_checker("bootstrap/named_core/wf.cl", term)
}

fn run_token_core_checker(term: &str) -> String {
    run_recursive_checker("bootstrap/token_core/wf.cl", term)
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
