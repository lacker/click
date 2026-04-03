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

fn apply_all(function: impl AsRef<str>, args: &[String]) -> String {
    let mut result = function.as_ref().to_string();
    for arg in args {
        result = app_expr(&result, arg);
    }
    result
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
fn close_recursive(worker: impl AsRef<str>) -> String {
    app_expr(load("bootstrap/base/fix.cl"), worker)
}

fn load_assoc_lookup() -> String {
    close_recursive(load("bootstrap/base/assoc.cl"))
}

fn load_structural_equal() -> String {
    close_recursive(load("bootstrap/base/structural_equal.cl"))
}

fn load_alpha_eq() -> String {
    let assoc_lookup = load_assoc_lookup();
    let structural_equal = load_structural_equal();
    let worker = apply_all(
        load("bootstrap/token_core/alpha_eq.cl"),
        &[assoc_lookup, structural_equal],
    );
    let alpha_eq = close_recursive(worker);
    format!(
        "(lambda lhs (lambda rhs {}))",
        apply_all(
            &alpha_eq,
            &[
                "(var lhs)".to_string(),
                "(var rhs)".to_string(),
                "nil".to_string(),
                "nil".to_string(),
                "'mark".to_string(),
            ]
        )
    )
}

fn load_subst() -> String {
    close_recursive(load("bootstrap/token_core/subst.cl"))
}

fn load_whnf() -> String {
    let subst = load_subst();
    let worker = apply_all(load("bootstrap/token_core/whnf.cl"), &[subst]);
    close_recursive(worker)
}

fn run_recursive_checker(worker_path: &str, term: &str) -> String {
    let checker = close_recursive(load(worker_path));
    let request = request("wf", term, "nil");
    eval(&app_expr(checker, request))
}

fn run_token_core_checker(term: &str) -> String {
    run_recursive_checker("bootstrap/token_core/wf.cl", term)
}

fn run_token_core_eval(term: &str) -> String {
    let assoc_lookup = load_assoc_lookup();
    let worker = apply_all(load("bootstrap/token_core/eval_env.cl"), &[assoc_lookup]);
    let evaluator = close_recursive(worker);
    let quoted_term = format!("(quote {term})");
    eval(&apply_all(evaluator, &[quoted_term, "nil".to_string()]))
}

fn run_token_core_infer(term: &str) -> String {
    let assoc_lookup = load_assoc_lookup();
    let alpha_eq = load_alpha_eq();
    let subst = load_subst();
    let whnf = load_whnf();
    let worker = apply_all(
        load("bootstrap/token_core/infer.cl"),
        &[assoc_lookup, alpha_eq, subst, whnf],
    );
    let infer = close_recursive(worker);
    let quoted_term = format!("(quote {term})");
    eval(&apply_all(infer, &[quoted_term, "nil".to_string()]))
}

fn run_token_core_typecheck(term: &str, expected_type: &str) -> String {
    let assoc_lookup = load_assoc_lookup();
    let alpha_eq = load_alpha_eq();
    let subst = load_subst();
    let whnf = load_whnf();
    let infer_worker = apply_all(
        load("bootstrap/token_core/infer.cl"),
        &[assoc_lookup.clone(), alpha_eq.clone(), subst, whnf.clone()],
    );
    let infer = close_recursive(infer_worker);
    let typechecker = apply_all(load("bootstrap/token_core/typecheck.cl"), &[infer, alpha_eq, whnf]);
    let quoted_term = format!("(quote {term})");
    let quoted_expected = format!("(quote {expected_type})");
    eval(&apply_all(
        typechecker,
        &[quoted_term, quoted_expected, "nil".to_string()],
    ))
}

fn load_bool_type() -> String {
    load("bootstrap/data/bool_type.cl")
}

fn load_bool_true() -> String {
    load("bootstrap/data/bool_true.cl")
}

fn load_bool_false() -> String {
    load("bootstrap/data/bool_false.cl")
}

fn load_bool_if() -> String {
    load("bootstrap/data/bool_if.cl")
}

fn load_eq_type() -> String {
    load("bootstrap/proofs/eq.cl")
}

fn load_refl() -> String {
    load("bootstrap/proofs/refl.cl")
}

#[test]
fn assoc_lookup_preserves_false_and_nil_values() {
    let assoc_lookup = load_assoc_lookup();

    assert_eq!(
        eval(&apply_all(
            &assoc_lookup,
            &["'x".to_string(), "'((x false) (y nil))".to_string()],
        )),
        "(found false)"
    );
    assert_eq!(
        eval(&apply_all(
            &assoc_lookup,
            &["'y".to_string(), "'((x false) (y nil))".to_string()],
        )),
        "(found nil)"
    );
    assert_eq!(
        eval(&apply_all(
            &assoc_lookup,
            &["'z".to_string(), "'((x false) (y nil))".to_string()],
        )),
        "missing"
    );
}

#[test]
fn structural_equal_matches_nested_lists() {
    let structural_equal = load_structural_equal();

    assert_eq!(
        eval(&apply_all(
            &structural_equal,
            &["'(a (b c))".to_string(), "'(a (b c))".to_string()],
        )),
        "true"
    );
    assert_eq!(
        eval(&apply_all(
            &structural_equal,
            &["'(a (b c))".to_string(), "'(a (b d))".to_string()],
        )),
        "false"
    );
    assert_eq!(
        eval(&apply_all(
            &structural_equal,
            &["'a".to_string(), "'(a)".to_string()],
        )),
        "false"
    );
}

#[test]
fn alpha_eq_matches_alpha_equivalent_token_core_terms() {
    let alpha_eq = load_alpha_eq();

    assert_eq!(
        eval(&apply_all(
            &alpha_eq,
            &[
                "'(pi x type (var x))".to_string(),
                "'(pi y type (var y))".to_string(),
            ],
        )),
        "true"
    );
    assert_eq!(
        eval(&apply_all(
            &alpha_eq,
            &[
                "'(lambda x type (var x))".to_string(),
                "'(lambda y type (var y))".to_string(),
            ],
        )),
        "true"
    );
    assert_eq!(
        eval(&apply_all(
            &alpha_eq,
            &[
                "'(lambda x type (var x))".to_string(),
                "'(lambda y type type)".to_string(),
            ],
        )),
        "false"
    );
}

#[test]
fn whnf_reduces_head_beta_redexes() {
    let whnf = load_whnf();

    assert_eq!(
        eval(&apply_all(
            &whnf,
            &["'(app (lambda X type (var X)) type)".to_string()],
        )),
        "type"
    );
    assert_eq!(
        eval(&apply_all(
            &whnf,
            &["'(app (lambda T type (pi x (var T) (var T))) type)".to_string()],
        )),
        "(pi x type type)"
    );
}

#[test]
fn subst_replaces_free_variables_and_respects_binders() {
    let subst = load_subst();

    assert_eq!(
        eval(&apply_all(
            &subst,
            &[
                "'(var x)".to_string(),
                "'x".to_string(),
                "'type".to_string()
            ],
        )),
        "type"
    );
    assert_eq!(
        eval(&apply_all(
            &subst,
            &[
                "'(lambda x type (var x))".to_string(),
                "'x".to_string(),
                "'type".to_string(),
            ],
        )),
        "(lambda x type (var x))"
    );
    assert_eq!(
        eval(&apply_all(
            &subst,
            &[
                "'(lambda y type (var x))".to_string(),
                "'x".to_string(),
                "'type".to_string(),
            ],
        )),
        "(lambda y type type)"
    );
}

#[test]
fn bool_layer_terms_typecheck() {
    assert_eq!(run_token_core_infer(&load_bool_type()), "(ok type)");
    assert_eq!(
        run_token_core_infer(&load_bool_true()),
        "(ok (pi A type (pi t (var A) (pi f (var A) (var A)))))"
    );
    assert_eq!(
        run_token_core_infer(&load_bool_false()),
        "(ok (pi A type (pi t (var A) (pi f (var A) (var A)))))"
    );
    assert_eq!(
        run_token_core_infer(&load_bool_if()),
        "(ok (pi b (pi A type (pi t (var A) (pi f (var A) (var A)))) (pi A type (pi t (var A) (pi f (var A) (var A))))))"
    );
}

#[test]
fn proof_terms_typecheck() {
    assert_eq!(
        run_token_core_infer(&load_eq_type()),
        "(ok (pi A type (pi x (var A) (pi y (var A) type))))"
    );
    assert_eq!(
        run_token_core_infer(&load_refl()),
        "(ok (pi A type (pi x (var A) (pi P (pi z (var A) type) (pi px (app (var P) (var x)) (app (var P) (var x)))))))"
    );
    assert_eq!(
        run_token_core_infer(&apply_all(
            load_refl(),
            &["type".to_string(), "(pi z type type)".to_string()],
        )),
        "(ok (pi P (pi z type type) (pi px (app (var P) (pi z type type)) (app (var P) (pi z type type)))))"
    );
}

#[test]
fn bool_layer_terms_evaluate() {
    let then_branch = "type".to_string();
    let else_branch = "(pi z type type)".to_string();

    assert_eq!(
        run_token_core_eval(&apply_all(
            load_bool_true(),
            &["type".to_string(), then_branch.clone(), else_branch.clone()],
        )),
        "(ok (type-value))"
    );
    assert_eq!(
        run_token_core_eval(&apply_all(
            load_bool_false(),
            &["type".to_string(), then_branch.clone(), else_branch.clone()],
        )),
        "(ok (pi-value z type type nil))"
    );
    assert_eq!(
        run_token_core_eval(&apply_all(
            load_bool_if(),
            &[
                load_bool_true(),
                "type".to_string(),
                then_branch.clone(),
                else_branch.clone(),
            ],
        )),
        "(ok (type-value))"
    );
    assert_eq!(
        run_token_core_eval(&apply_all(
            load_bool_if(),
            &[
                load_bool_false(),
                "type".to_string(),
                then_branch,
                else_branch,
            ],
        )),
        "(ok (pi-value z type type nil))"
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

#[test]
fn token_core_eval_handles_small_terms() {
    assert_eq!(run_token_core_eval("type"), "(ok (type-value))");
    assert_eq!(
        run_token_core_eval("(lambda x type (var x))"),
        "(ok (closure x (var x) nil))"
    );
    assert_eq!(
        run_token_core_eval("(pi x type type)"),
        "(ok (pi-value x type type nil))"
    );
    assert_eq!(
        run_token_core_eval("(app (lambda x type (var x)) type)"),
        "(ok (type-value))"
    );
}

#[test]
fn token_core_eval_reports_errors() {
    assert_eq!(run_token_core_eval("(var x)"), "(err unbound-variable)");
    assert_eq!(
        run_token_core_eval("(app type type)"),
        "(err not-a-function)"
    );
    assert_eq!(run_token_core_eval("(lambda x type)"), "(err bad-lambda)");
    assert_eq!(
        run_token_core_eval("(app (lambda x type (lambda x type (var x))) type)"),
        "(err duplicate-binder)"
    );
}

#[test]
fn token_core_infer_accepts_small_terms() {
    assert_eq!(run_token_core_infer("type"), "(ok type)");
    assert_eq!(run_token_core_infer("(pi x type type)"), "(ok type)");
    assert_eq!(
        run_token_core_infer("(lambda x type (var x))"),
        "(ok (pi x type type))"
    );
    assert_eq!(
        run_token_core_infer("(app (lambda x type (var x)) type)"),
        "(ok type)"
    );
    assert_eq!(
        run_token_core_infer(
            "(app (lambda f (pi x type type) (app (var f) type)) (lambda y type (var y)))"
        ),
        "(ok type)"
    );
    assert_eq!(
        run_token_core_infer(
            "(app (lambda f (app (lambda T type (pi x (var T) (var T))) type) (app (var f) type)) (lambda y type (var y)))"
        ),
        "(ok type)"
    );
}

#[test]
fn token_core_infer_reports_errors() {
    assert_eq!(
        run_token_core_infer("(var x)"),
        "(err unbound-variable)"
    );
    assert_eq!(
        run_token_core_infer("(lambda x type (lambda x type (var x)))"),
        "(err duplicate-binder)"
    );
    assert_eq!(
        run_token_core_infer("(pi x (lambda y type (var y)) type)"),
        "(err bad-domain-type)"
    );
    assert_eq!(
        run_token_core_infer("(app (lambda x type (var x)) (lambda y type (var y)))"),
        "(err argument-type-mismatch)"
    );
    assert_eq!(
        run_token_core_infer("(lambda x type)"),
        "(err bad-lambda)"
    );
}

#[test]
fn token_core_typecheck_accepts_expected_types() {
    assert_eq!(run_token_core_typecheck("type", "type"), "(ok type)");
    assert_eq!(
        run_token_core_typecheck("(lambda x type (var x))", "(pi y type type)"),
        "(ok (pi y type type))"
    );
    assert_eq!(
        run_token_core_typecheck(
            &load_refl(),
            "(pi A type (pi x (var A) (pi P (pi z (var A) type) (pi px (app (var P) (var x)) (app (var P) (var x))))))"
        ),
        "(ok (pi A type (pi x (var A) (pi P (pi z (var A) type) (pi px (app (var P) (var x)) (app (var P) (var x)))))))"
    );
}

#[test]
fn token_core_typecheck_reports_mismatches() {
    assert_eq!(
        run_token_core_typecheck("(lambda x type (var x))", "(pi y type (pi z type type))"),
        "(err type-mismatch)"
    );
    assert_eq!(
        run_token_core_typecheck("(app type type)", "type"),
        "(err not-a-pi)"
    );
}
