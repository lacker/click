//! Prelude loader tests.

use super::*;
use crate::{
    Computation, ComputationDefinitionError, LAMBDA_KIND_SYMBOL, LIST_KIND_SYMBOL, Proof,
    SYMBOL_KIND_SYMBOL, Step, Theorem, TheoremError, computes_to_list, elab::proof, is_list,
};

fn computation(spelling: &str) -> Name {
    computation_name(spelling).expect("prelude should define requested computation")
}

fn theorem(spelling: &str) -> Name {
    theorem_name(spelling).expect("prelude should define requested theorem")
}

fn symbol(spelling: &str) -> Symbol {
    symbol_name(spelling).expect("prelude should define requested symbol")
}

fn computation_ref(spelling: &str) -> Computation {
    Computation::Ref(computation(spelling))
}

fn checked_theorem(spelling: &str) -> Option<Theorem> {
    theory().known(theorem(spelling))
}

fn reverse_acc() -> Computation {
    computation_ref("reverse_acc")
}

fn reverse() -> Computation {
    computation_ref("reverse")
}

fn append() -> Computation {
    computation_ref("append")
}

fn snoc() -> Computation {
    computation_ref("snoc")
}

fn concat() -> Computation {
    computation_ref("concat")
}

fn map() -> Computation {
    computation_ref("map")
}

fn concat_map() -> Computation {
    computation_ref("concat-map")
}

fn fold_right() -> Computation {
    computation_ref("fold-right")
}

fn fold_left() -> Computation {
    computation_ref("fold-left")
}

fn zip_with() -> Computation {
    computation_ref("zip-with")
}

fn filter() -> Computation {
    computation_ref("filter")
}

fn any() -> Computation {
    computation_ref("any")
}

fn all() -> Computation {
    computation_ref("all")
}

fn is_symbol() -> Computation {
    computation_ref("is-symbol")
}

fn is_lambda() -> Computation {
    computation_ref("is-lambda")
}

fn is_list_value() -> Computation {
    computation_ref("is-list-value")
}

fn value_eq() -> Computation {
    computation_ref("value-eq")
}

fn member() -> Computation {
    computation_ref("member")
}

fn last() -> Computation {
    computation_ref("last")
}

fn init() -> Computation {
    computation_ref("init")
}

fn null() -> Computation {
    computation_ref("null")
}

fn is_singleton() -> Computation {
    computation_ref("is-singleton")
}

fn zero() -> Computation {
    computation_ref("zero")
}

fn succ() -> Computation {
    computation_ref("succ")
}

fn is_nat_value() -> Computation {
    computation_ref("is-nat-value")
}

fn add() -> Computation {
    computation_ref("add")
}

fn parse_test_module(source: &str) -> (source::ParsedModule, ElabEnv) {
    let mut env = prelude_env();
    let module = env
        .parse_module(source)
        .expect("synthetic module should parse");
    (module, env)
}

fn prelude_theorem_names() -> Vec<Name> {
    [
        "reverse_acc_computes_to_list",
        "reverse_computes_to_list",
        "reverse_nil_computes_to_list",
        "reverse_nil",
        "reverse_singleton",
        "append_nil_computes_to_list",
        "append_computes_to_list",
        "append_nil_returns_right",
        "append_right_nil",
        "append_cons",
        "append_singleton",
        "append_assoc",
        "reverse_acc_append",
        "reverse_cons",
        "reverse_acc_reverse",
        "reverse_double",
        "reverse_acc_of_append",
        "reverse_append",
        "snoc_computes_to_list",
        "snoc_nil",
        "snoc_cons",
        "concat_nil",
        "map_nil",
        "map_cons",
        "map_computes_to_list",
        "concat_map_nil",
        "concat_map_cons",
        "concat_map_computes_to_list",
        "fold_right_nil",
        "fold_right_cons",
        "fold_right_computes_to_value",
        "fold_left_nil",
        "fold_left_cons",
        "fold_left_computes_to_value",
        "zip_with_left_nil",
        "zip_with_right_nil",
        "zip_with_cons",
        "zip_with_computes_to_list",
        "filter_nil",
        "filter_cons_true",
        "filter_cons_false",
        "filter_computes_to_list",
        "any_nil",
        "any_cons_true",
        "any_cons_false",
        "any_computes_to_bool",
        "value_eq_true_true",
        "value_eq_true_false",
        "value_eq_nil",
        "value_eq_nil_cons",
        "value_eq_cons_nil",
        "value_eq_cons",
        "member_nil",
        "member_cons_true",
        "member_cons_false",
        "all_nil",
        "all_cons_true",
        "all_cons_false",
        "all_computes_to_bool",
        "map_identity",
        "concat_map_singleton",
        "fold_right_cons_nil",
        "fold_left_reverse_acc",
        "fold_left_reverse",
        "last_nil_errors",
        "last_singleton",
        "last_cons",
        "init_nil_errors",
        "init_singleton",
        "init_cons",
        "null_nil",
        "null_cons",
        "is_singleton_nil",
        "is_singleton_singleton",
        "is_singleton_cons",
        "add_is_append",
        "zero_computes_to_list",
        "zero_is_nat_value",
        "succ_zero",
        "succ_computes_to_list",
        "succ_preserves_nat_value",
        "is_nat_value_cons",
        "add_zero_left",
        "add_computes_to_list",
        "add_cons",
        "add_succ_left",
        "add_zero_right",
        "add_nat_suffix_preserves_nat_value",
        "add_preserves_nat_value",
        "add_assoc",
    ]
    .into_iter()
    .map(theorem)
    .collect()
}

#[test]
fn loaded_prelude_exposes_theory_and_source_environment() {
    let loaded = loaded();

    assert_eq!(loaded.computation("append"), Some(computation("append")));
    assert_eq!(loaded.computation("zero"), Some(computation("zero")));
    assert_eq!(
        loaded.theorem("append_assoc"),
        Some(theorem("append_assoc"))
    );
    assert_eq!(
        loaded.theorem("add_computes_to_list"),
        Some(theorem("add_computes_to_list"))
    );
    assert_eq!(loaded.symbol(":true"), Some(symbol(":true")));
    assert_eq!(loaded.symbol(":false"), Some(symbol(":false")));
    assert_eq!(loaded.symbol(":symbol"), Some(SYMBOL_KIND_SYMBOL));
    assert_eq!(loaded.symbol(":lambda"), Some(LAMBDA_KIND_SYMBOL));
    assert_eq!(loaded.symbol(":list"), Some(LIST_KIND_SYMBOL));
    assert_eq!(loaded.computation("missing"), None);
    assert_eq!(loaded.theorem("missing"), None);
    assert_eq!(loaded.symbol("missing"), None);
    assert_eq!(
        loaded.theory().computation(computation("append")),
        Some(&list_tests::append_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("zero")),
        Some(&nat_tests::zero_definition())
    );
    assert_eq!(
        loaded.theory().theorem(theorem("append_assoc")),
        Some(&list_tests::append_assoc_source_theorem())
    );
    assert_eq!(
        loaded.theory().theorem(theorem("add_computes_to_list")),
        Some(&nat_tests::add_computes_to_list_source_theorem())
    );
    assert_eq!(
        loaded.env().computation("reverse_acc"),
        Some(computation("reverse_acc"))
    );

    assert_eq!(
        computation_name("is-singleton"),
        Some(computation("is-singleton"))
    );
    assert_eq!(
        theorem_name("reverse_double"),
        Some(theorem("reverse_double"))
    );
    assert_eq!(symbol_name(":true"), Some(symbol(":true")));
    assert_eq!(symbol_name(":symbol"), Some(SYMBOL_KIND_SYMBOL));
    assert_eq!(symbol_name(":lambda"), Some(LAMBDA_KIND_SYMBOL));
    assert_eq!(symbol_name(":list"), Some(LIST_KIND_SYMBOL));
    assert_eq!(computation_name("zero"), Some(computation("zero")));
    assert_eq!(
        theorem_name("add_computes_to_list"),
        Some(theorem("add_computes_to_list"))
    );
}

#[test]
fn loaded_computation_prelude_keeps_env_without_defining_theorems() {
    let loaded = loaded_computations();

    assert_eq!(loaded.computation("reverse"), Some(computation("reverse")));
    assert_eq!(loaded.computation("add"), Some(computation("add")));
    assert_eq!(
        loaded.theorem("append_assoc"),
        Some(theorem("append_assoc"))
    );
    assert_eq!(
        loaded.theorem("add_computes_to_list"),
        Some(theorem("add_computes_to_list"))
    );
    assert_eq!(
        loaded.theory().computation(computation("reverse")),
        Some(&list_tests::reverse_definition())
    );
    assert_eq!(
        loaded.theory().computation(computation("add")),
        Some(&nat_tests::add_definition())
    );
    assert!(loaded.theory().theorem(theorem("append_assoc")).is_none());
    assert!(
        loaded
            .theory()
            .theorem(theorem("add_computes_to_list"))
            .is_none()
    );
}

#[test]
fn theory_defines_reverse() {
    let theory = theory();
    let try_theory = try_theory().expect("prelude should load");

    assert_eq!(
        theory.computation(computation("reverse_acc")),
        Some(&list_tests::reverse_acc_definition())
    );
    assert_eq!(
        try_theory.computation(computation("reverse_acc")),
        Some(&list_tests::reverse_acc_definition())
    );
    assert_eq!(
        theory.computation(computation("reverse")),
        Some(&list_tests::reverse_definition())
    );
    assert_eq!(
        theory.computation(computation("append")),
        Some(&list_tests::append_definition())
    );
    assert_eq!(
        theory.computation(computation("snoc")),
        Some(&list_tests::snoc_definition())
    );
    assert_eq!(
        theory.computation(computation("concat")),
        Some(&list_tests::concat_definition())
    );
    assert_eq!(
        theory.computation(computation("map")),
        Some(&list_tests::map_definition())
    );
    assert_eq!(
        theory.computation(computation("concat-map")),
        Some(&list_tests::concat_map_definition())
    );
    assert_eq!(
        theory.computation(computation("fold-right")),
        Some(&list_tests::fold_right_definition())
    );
    assert_eq!(
        theory.computation(computation("fold-left")),
        Some(&list_tests::fold_left_definition())
    );
    assert_eq!(
        theory.computation(computation("zip-with")),
        Some(&list_tests::zip_with_definition())
    );
    assert_eq!(
        theory.computation(computation("filter")),
        Some(&list_tests::filter_definition())
    );
    assert_eq!(
        theory.computation(computation("any")),
        Some(&list_tests::any_definition())
    );
    assert_eq!(
        theory.computation(computation("all")),
        Some(&list_tests::all_definition())
    );
    assert_eq!(
        theory.computation(computation("is-symbol")),
        Some(&list_tests::is_symbol_definition())
    );
    assert_eq!(
        theory.computation(computation("is-lambda")),
        Some(&list_tests::is_lambda_definition())
    );
    assert_eq!(
        theory.computation(computation("is-list-value")),
        Some(&list_tests::is_list_value_definition())
    );
    assert_eq!(
        theory.computation(computation("value-eq")),
        Some(&list_tests::value_eq_definition())
    );
    assert_eq!(
        theory.computation(computation("member")),
        Some(&list_tests::member_definition())
    );
    assert_eq!(
        theory.computation(computation("last")),
        Some(&list_tests::last_definition())
    );
    assert_eq!(
        theory.computation(computation("init")),
        Some(&list_tests::init_definition())
    );
    assert_eq!(
        theory.computation(computation("null")),
        Some(&list_tests::null_definition())
    );
    assert_eq!(
        theory.computation(computation("is-singleton")),
        Some(&list_tests::is_singleton_definition())
    );
    assert_eq!(
        theory.computation(computation("zero")),
        Some(&nat_tests::zero_definition())
    );
    assert_eq!(
        theory.computation(computation("succ")),
        Some(&nat_tests::succ_definition())
    );
    assert_eq!(
        theory.computation(computation("is-nat-value")),
        Some(&nat_tests::is_nat_value_definition())
    );
    assert_eq!(
        theory.computation(computation("add")),
        Some(&nat_tests::add_definition())
    );
    assert_eq!(reverse_acc(), Computation::Ref(computation("reverse_acc")));
    assert_eq!(reverse(), Computation::Ref(computation("reverse")));
    assert_eq!(append(), Computation::Ref(computation("append")));
    assert_eq!(snoc(), Computation::Ref(computation("snoc")));
    assert_eq!(concat(), Computation::Ref(computation("concat")));
    assert_eq!(map(), Computation::Ref(computation("map")));
    assert_eq!(concat_map(), Computation::Ref(computation("concat-map")));
    assert_eq!(fold_right(), Computation::Ref(computation("fold-right")));
    assert_eq!(fold_left(), Computation::Ref(computation("fold-left")));
    assert_eq!(zip_with(), Computation::Ref(computation("zip-with")));
    assert_eq!(filter(), Computation::Ref(computation("filter")));
    assert_eq!(any(), Computation::Ref(computation("any")));
    assert_eq!(all(), Computation::Ref(computation("all")));
    assert_eq!(is_symbol(), Computation::Ref(computation("is-symbol")));
    assert_eq!(is_lambda(), Computation::Ref(computation("is-lambda")));
    assert_eq!(
        is_list_value(),
        Computation::Ref(computation("is-list-value"))
    );
    assert_eq!(value_eq(), Computation::Ref(computation("value-eq")));
    assert_eq!(member(), Computation::Ref(computation("member")));
    assert_eq!(last(), Computation::Ref(computation("last")));
    assert_eq!(init(), Computation::Ref(computation("init")));
    assert_eq!(null(), Computation::Ref(computation("null")));
    assert_eq!(
        is_singleton(),
        Computation::Ref(computation("is-singleton"))
    );
    assert_eq!(zero(), Computation::Ref(computation("zero")));
    assert_eq!(succ(), Computation::Ref(computation("succ")));
    assert_eq!(
        is_nat_value(),
        Computation::Ref(computation("is-nat-value"))
    );
    assert_eq!(add(), Computation::Ref(computation("add")));
    assert_eq!(
        theory.reduce(&reverse_acc()),
        Step::Reduced(list_tests::reverse_acc_definition())
    );
    assert_eq!(
        theory.reduce(&reverse()),
        Step::Reduced(list_tests::reverse_definition())
    );
    assert_eq!(
        theory.reduce(&append()),
        Step::Reduced(list_tests::append_definition())
    );
    assert_eq!(
        theory.reduce(&snoc()),
        Step::Reduced(list_tests::snoc_definition())
    );
    assert_eq!(
        theory.reduce(&concat()),
        Step::Reduced(list_tests::concat_definition())
    );
    assert_eq!(
        theory.reduce(&map()),
        Step::Reduced(list_tests::map_definition())
    );
    assert_eq!(
        theory.reduce(&concat_map()),
        Step::Reduced(list_tests::concat_map_definition())
    );
    assert_eq!(
        theory.reduce(&fold_right()),
        Step::Reduced(list_tests::fold_right_definition())
    );
    assert_eq!(
        theory.reduce(&fold_left()),
        Step::Reduced(list_tests::fold_left_definition())
    );
    assert_eq!(
        theory.reduce(&zip_with()),
        Step::Reduced(list_tests::zip_with_definition())
    );
    assert_eq!(
        theory.reduce(&filter()),
        Step::Reduced(list_tests::filter_definition())
    );
    assert_eq!(
        theory.reduce(&any()),
        Step::Reduced(list_tests::any_definition())
    );
    assert_eq!(
        theory.reduce(&all()),
        Step::Reduced(list_tests::all_definition())
    );
    assert_eq!(
        theory.reduce(&is_symbol()),
        Step::Reduced(list_tests::is_symbol_definition())
    );
    assert_eq!(
        theory.reduce(&is_lambda()),
        Step::Reduced(list_tests::is_lambda_definition())
    );
    assert_eq!(
        theory.reduce(&is_list_value()),
        Step::Reduced(list_tests::is_list_value_definition())
    );
    assert_eq!(
        theory.reduce(&value_eq()),
        Step::Reduced(list_tests::value_eq_definition())
    );
    assert_eq!(
        theory.reduce(&member()),
        Step::Reduced(list_tests::member_definition())
    );
    assert_eq!(
        theory.reduce(&last()),
        Step::Reduced(list_tests::last_definition())
    );
    assert_eq!(
        theory.reduce(&init()),
        Step::Reduced(list_tests::init_definition())
    );
    assert_eq!(
        theory.reduce(&null()),
        Step::Reduced(list_tests::null_definition())
    );
    assert_eq!(
        theory.reduce(&is_singleton()),
        Step::Reduced(list_tests::is_singleton_definition())
    );
    assert_eq!(
        theory.reduce(&zero()),
        Step::Reduced(nat_tests::zero_definition())
    );
    assert_eq!(
        theory.reduce(&succ()),
        Step::Reduced(nat_tests::succ_definition())
    );
    assert_eq!(
        theory.reduce(&is_nat_value()),
        Step::Reduced(nat_tests::is_nat_value_definition())
    );
    assert_eq!(
        theory.reduce(&add()),
        Step::Reduced(nat_tests::add_definition())
    );
}

#[test]
fn computation_theory_does_not_define_theorems() {
    let theory = computation_theory();
    let try_theory = try_computation_theory().expect("prelude computations should load");

    for theorem in prelude_theorem_names() {
        assert!(theory.theorem(theorem).is_none());
        assert!(try_theory.theorem(theorem).is_none());
    }
}

#[test]
fn computation_definition_diagnostics_report_kernel_rejection() {
    let mut theory = Theory::new();

    assert!(theory.define_computation(computation("reverse_acc"), &Computation::Nil));
    assert!(!define_computations_in_theory(&mut theory));
    assert_eq!(
        try_define_computations_in_theory(&mut theory),
        Err(SourceComputationError::ComputationRejected {
            computation: computation("reverse_acc"),
            error: ComputationDefinitionError::ComputationNameAlreadyDefined(computation(
                "reverse_acc"
            )),
        })
    );
}

#[test]
fn full_source_load_diagnostics_report_computation_failures() {
    let mut theory = Theory::new();

    assert!(theory.define_computation(computation("reverse_acc"), &Computation::Nil));
    assert!(!define_in_theory(&mut theory));
    assert_eq!(
        try_define_in_theory(&mut theory),
        Err(SourceLoadError::Computation(
            SourceComputationError::ComputationRejected {
                computation: computation("reverse_acc"),
                error: ComputationDefinitionError::ComputationNameAlreadyDefined(computation(
                    "reverse_acc"
                )),
            }
        ))
    );
}

#[test]
fn theorem_definitions_require_computations() {
    let mut theory = Theory::new();

    assert!(!define_theorems_in_theory(&mut theory));
    let Err(SourceTheoremError::ProofElaborationFailed {
        theorem: failed_theorem,
        error,
    }) = try_define_theorems_in_theory(&mut theory)
    else {
        panic!("theorem loading should report proof elaboration failure");
    };
    assert_eq!(failed_theorem, theorem("reverse_acc_computes_to_list"));
    assert!(proof_error_contains_evaluation_failure(&error));

    for theorem in prelude_theorem_names() {
        assert!(theory.theorem(theorem).is_none());
    }
}

#[test]
fn full_source_load_diagnostics_report_theorem_failures() {
    let (module, env) = parse_test_module(
        "
            (theorem bad
              (equal nil (quote unit))
              (proof (eval-to nil nil)))
            ",
    );
    let bad = env
        .theorem("bad")
        .expect("module should define bad theorem");
    let mut theory = Theory::new();

    assert_eq!(
        define_module_in_theory_result(&mut theory, &module),
        Err(SourceLoadError::Theorem(
            SourceTheoremError::TheoremRejected {
                theorem: bad,
                error: TheoremError::InvalidProof,
            }
        ))
    );
}

fn proof_error_contains_evaluation_failure(error: &ProofElaborationError) -> bool {
    match error {
        ProofElaborationError::EvaluationFailed(_) => true,
        ProofElaborationError::InSubproof { error, .. } => {
            proof_error_contains_evaluation_failure(error)
        }
        ProofElaborationError::UnknownTheorem(_) => false,
        ProofElaborationError::TacticFailed { .. } => false,
    }
}

#[test]
fn source_theorem_diagnostics_report_kernel_rejection() {
    let (module, env) = parse_test_module(
        "
            (theorem bad
              (equal nil (quote unit))
              (proof (eval-to nil nil)))
            ",
    );
    let bad = env
        .theorem("bad")
        .expect("module should define bad theorem");

    assert_eq!(
        proof::source_theorem_result(module, bad, Theory::new()),
        Err(SourceTheoremError::TheoremRejected {
            theorem: bad,
            error: TheoremError::InvalidProof,
        })
    );
}

#[test]
fn source_theorem_diagnostics_report_unknown_known_theorem() {
    let (module, env) = parse_test_module(
        "
            (theorem bad
              (equal nil nil)
              (proof (known later)))
            (theorem later
              (equal nil nil)
              (proof (eval-to nil nil)))
            ",
    );
    let bad = env
        .theorem("bad")
        .expect("module should define bad theorem");
    let later = env
        .theorem("later")
        .expect("module should define later theorem");

    assert_eq!(
        proof::source_theorem_result(module, bad, Theory::new()),
        Err(SourceTheoremError::ProofElaborationFailed {
            theorem: bad,
            error: ProofElaborationError::UnknownTheorem(later),
        })
    );
}

#[test]
fn theory_defines_reverse_theorems() {
    let theory = theory();
    let reverse_acc_prop = list_tests::reverse_acc_computes_to_list_source_theorem();
    let reverse_prop = list_tests::reverse_computes_to_list_source_theorem();
    let reverse_nil_prop = list_tests::reverse_nil_computes_to_list_source_theorem();
    let reverse_nil_exact_prop = list_tests::reverse_nil_source_theorem();
    let reverse_singleton_prop = list_tests::reverse_singleton_source_theorem();
    let reverse_acc_append_prop = list_tests::reverse_acc_append_source_theorem();
    let reverse_cons_prop = list_tests::reverse_cons_source_theorem();
    let reverse_acc_reverse_prop = list_tests::reverse_acc_reverse_source_theorem();
    let reverse_double_prop = list_tests::reverse_double_source_theorem();
    let reverse_acc_of_append_prop = list_tests::reverse_acc_of_append_source_theorem();
    let reverse_append_prop = list_tests::reverse_append_source_theorem();
    let snoc_prop = list_tests::snoc_computes_to_list_source_theorem();
    let snoc_nil_prop = list_tests::snoc_nil_source_theorem();
    let snoc_cons_prop = list_tests::snoc_cons_source_theorem();
    let concat_nil_prop = list_tests::concat_nil_source_theorem();
    let map_nil_prop = list_tests::map_nil_source_theorem();
    let map_cons_prop = list_tests::map_cons_source_theorem();
    let map_computes_to_list_prop = list_tests::map_computes_to_list_source_theorem();
    let concat_map_nil_prop = list_tests::concat_map_nil_source_theorem();
    let concat_map_cons_prop = list_tests::concat_map_cons_source_theorem();
    let concat_map_computes_to_list_prop = list_tests::concat_map_computes_to_list_source_theorem();
    let fold_right_nil_prop = list_tests::fold_right_nil_source_theorem();
    let fold_right_cons_prop = list_tests::fold_right_cons_source_theorem();
    let fold_right_computes_to_value_prop =
        list_tests::fold_right_computes_to_value_source_theorem();
    let fold_left_nil_prop = list_tests::fold_left_nil_source_theorem();
    let fold_left_cons_prop = list_tests::fold_left_cons_source_theorem();
    let fold_left_computes_to_value_prop = list_tests::fold_left_computes_to_value_source_theorem();
    let zip_with_left_nil_prop = list_tests::zip_with_left_nil_source_theorem();
    let zip_with_right_nil_prop = list_tests::zip_with_right_nil_source_theorem();
    let zip_with_cons_prop = list_tests::zip_with_cons_source_theorem();
    let zip_with_computes_to_list_prop = list_tests::zip_with_computes_to_list_source_theorem();
    let filter_nil_prop = list_tests::filter_nil_source_theorem();
    let filter_cons_true_prop = list_tests::filter_cons_true_source_theorem();
    let filter_cons_false_prop = list_tests::filter_cons_false_source_theorem();
    let filter_computes_to_list_prop = list_tests::filter_computes_to_list_source_theorem();
    let any_nil_prop = list_tests::any_nil_source_theorem();
    let any_cons_true_prop = list_tests::any_cons_true_source_theorem();
    let any_cons_false_prop = list_tests::any_cons_false_source_theorem();
    let any_computes_to_bool_prop = list_tests::any_computes_to_bool_source_theorem();
    let value_eq_true_true_prop = list_tests::value_eq_true_true_source_theorem();
    let value_eq_true_false_prop = list_tests::value_eq_true_false_source_theorem();
    let value_eq_nil_prop = list_tests::value_eq_nil_source_theorem();
    let value_eq_nil_cons_prop = list_tests::value_eq_nil_cons_source_theorem();
    let value_eq_cons_nil_prop = list_tests::value_eq_cons_nil_source_theorem();
    let value_eq_cons_prop = list_tests::value_eq_cons_source_theorem();
    let member_nil_prop = list_tests::member_nil_source_theorem();
    let member_cons_true_prop = list_tests::member_cons_true_source_theorem();
    let member_cons_false_prop = list_tests::member_cons_false_source_theorem();
    let all_nil_prop = list_tests::all_nil_source_theorem();
    let all_cons_true_prop = list_tests::all_cons_true_source_theorem();
    let all_cons_false_prop = list_tests::all_cons_false_source_theorem();
    let all_computes_to_bool_prop = list_tests::all_computes_to_bool_source_theorem();
    let map_identity_prop = list_tests::map_identity_source_theorem();
    let concat_map_singleton_prop = list_tests::concat_map_singleton_source_theorem();
    let fold_right_cons_nil_prop = list_tests::fold_right_cons_nil_source_theorem();
    let fold_left_reverse_acc_prop = list_tests::fold_left_reverse_acc_source_theorem();
    let fold_left_reverse_prop = list_tests::fold_left_reverse_source_theorem();
    let last_nil_errors_prop = list_tests::last_nil_errors_source_theorem();
    let last_singleton_prop = list_tests::last_singleton_source_theorem();
    let last_cons_prop = list_tests::last_cons_source_theorem();
    let init_nil_errors_prop = list_tests::init_nil_errors_source_theorem();
    let init_singleton_prop = list_tests::init_singleton_source_theorem();
    let init_cons_prop = list_tests::init_cons_source_theorem();
    let null_nil_prop = list_tests::null_nil_source_theorem();
    let null_cons_prop = list_tests::null_cons_source_theorem();
    let is_singleton_nil_prop = list_tests::is_singleton_nil_source_theorem();
    let is_singleton_singleton_prop = list_tests::is_singleton_singleton_source_theorem();
    let is_singleton_cons_prop = list_tests::is_singleton_cons_source_theorem();
    let append_nil_prop = list_tests::append_nil_computes_to_list_source_theorem();
    let append_prop = list_tests::append_computes_to_list_source_theorem();
    let append_nil_returns_right_prop = list_tests::append_nil_returns_right_source_theorem();
    let append_right_nil_prop = list_tests::append_right_nil_source_theorem();
    let append_cons_prop = list_tests::append_cons_source_theorem();
    let append_singleton_prop = list_tests::append_singleton_source_theorem();
    let append_assoc_prop = list_tests::append_assoc_source_theorem();

    assert_eq!(
        theory.theorem(theorem("reverse_acc_computes_to_list")),
        Some(&reverse_acc_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reverse_computes_to_list")),
        Some(&reverse_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reverse_nil_computes_to_list")),
        Some(&reverse_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reverse_nil")),
        Some(&reverse_nil_exact_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reverse_singleton")),
        Some(&reverse_singleton_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reverse_acc_append")),
        Some(&reverse_acc_append_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reverse_cons")),
        Some(&reverse_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reverse_acc_reverse")),
        Some(&reverse_acc_reverse_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reverse_double")),
        Some(&reverse_double_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reverse_acc_of_append")),
        Some(&reverse_acc_of_append_prop)
    );
    assert_eq!(
        theory.theorem(theorem("reverse_append")),
        Some(&reverse_append_prop)
    );
    assert_eq!(
        theory.theorem(theorem("snoc_computes_to_list")),
        Some(&snoc_prop)
    );
    assert_eq!(theory.theorem(theorem("snoc_nil")), Some(&snoc_nil_prop));
    assert_eq!(theory.theorem(theorem("snoc_cons")), Some(&snoc_cons_prop));
    assert_eq!(
        theory.theorem(theorem("concat_nil")),
        Some(&concat_nil_prop)
    );
    assert_eq!(theory.theorem(theorem("map_nil")), Some(&map_nil_prop));
    assert_eq!(theory.theorem(theorem("map_cons")), Some(&map_cons_prop));
    assert_eq!(
        theory.theorem(theorem("map_computes_to_list")),
        Some(&map_computes_to_list_prop)
    );
    assert_eq!(
        theory.theorem(theorem("concat_map_nil")),
        Some(&concat_map_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("concat_map_cons")),
        Some(&concat_map_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("concat_map_computes_to_list")),
        Some(&concat_map_computes_to_list_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_right_nil")),
        Some(&fold_right_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_right_cons")),
        Some(&fold_right_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_right_computes_to_value")),
        Some(&fold_right_computes_to_value_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_left_nil")),
        Some(&fold_left_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_left_cons")),
        Some(&fold_left_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_left_computes_to_value")),
        Some(&fold_left_computes_to_value_prop)
    );
    assert_eq!(
        theory.theorem(theorem("zip_with_left_nil")),
        Some(&zip_with_left_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("zip_with_right_nil")),
        Some(&zip_with_right_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("zip_with_cons")),
        Some(&zip_with_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("zip_with_computes_to_list")),
        Some(&zip_with_computes_to_list_prop)
    );
    assert_eq!(
        theory.theorem(theorem("filter_nil")),
        Some(&filter_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("filter_cons_true")),
        Some(&filter_cons_true_prop)
    );
    assert_eq!(
        theory.theorem(theorem("filter_cons_false")),
        Some(&filter_cons_false_prop)
    );
    assert_eq!(
        theory.theorem(theorem("filter_computes_to_list")),
        Some(&filter_computes_to_list_prop)
    );
    assert_eq!(theory.theorem(theorem("any_nil")), Some(&any_nil_prop));
    assert_eq!(
        theory.theorem(theorem("any_cons_true")),
        Some(&any_cons_true_prop)
    );
    assert_eq!(
        theory.theorem(theorem("any_cons_false")),
        Some(&any_cons_false_prop)
    );
    assert_eq!(
        theory.theorem(theorem("any_computes_to_bool")),
        Some(&any_computes_to_bool_prop)
    );
    assert_eq!(
        theory.theorem(theorem("value_eq_true_true")),
        Some(&value_eq_true_true_prop)
    );
    assert_eq!(
        theory.theorem(theorem("value_eq_true_false")),
        Some(&value_eq_true_false_prop)
    );
    assert_eq!(
        theory.theorem(theorem("value_eq_nil")),
        Some(&value_eq_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("value_eq_nil_cons")),
        Some(&value_eq_nil_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("value_eq_cons_nil")),
        Some(&value_eq_cons_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("value_eq_cons")),
        Some(&value_eq_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("member_nil")),
        Some(&member_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("member_cons_true")),
        Some(&member_cons_true_prop)
    );
    assert_eq!(
        theory.theorem(theorem("member_cons_false")),
        Some(&member_cons_false_prop)
    );
    assert_eq!(theory.theorem(theorem("all_nil")), Some(&all_nil_prop));
    assert_eq!(
        theory.theorem(theorem("all_cons_true")),
        Some(&all_cons_true_prop)
    );
    assert_eq!(
        theory.theorem(theorem("all_cons_false")),
        Some(&all_cons_false_prop)
    );
    assert_eq!(
        theory.theorem(theorem("all_computes_to_bool")),
        Some(&all_computes_to_bool_prop)
    );
    assert_eq!(
        theory.theorem(theorem("map_identity")),
        Some(&map_identity_prop)
    );
    assert_eq!(
        theory.theorem(theorem("concat_map_singleton")),
        Some(&concat_map_singleton_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_right_cons_nil")),
        Some(&fold_right_cons_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_left_reverse_acc")),
        Some(&fold_left_reverse_acc_prop)
    );
    assert_eq!(
        theory.theorem(theorem("fold_left_reverse")),
        Some(&fold_left_reverse_prop)
    );
    assert_eq!(
        theory.theorem(theorem("last_nil_errors")),
        Some(&last_nil_errors_prop)
    );
    assert_eq!(
        theory.theorem(theorem("last_singleton")),
        Some(&last_singleton_prop)
    );
    assert_eq!(theory.theorem(theorem("last_cons")), Some(&last_cons_prop));
    assert_eq!(
        theory.theorem(theorem("init_nil_errors")),
        Some(&init_nil_errors_prop)
    );
    assert_eq!(
        theory.theorem(theorem("init_singleton")),
        Some(&init_singleton_prop)
    );
    assert_eq!(theory.theorem(theorem("init_cons")), Some(&init_cons_prop));
    assert_eq!(theory.theorem(theorem("null_nil")), Some(&null_nil_prop));
    assert_eq!(theory.theorem(theorem("null_cons")), Some(&null_cons_prop));
    assert_eq!(
        theory.theorem(theorem("is_singleton_nil")),
        Some(&is_singleton_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("is_singleton_singleton")),
        Some(&is_singleton_singleton_prop)
    );
    assert_eq!(
        theory.theorem(theorem("is_singleton_cons")),
        Some(&is_singleton_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("append_nil_computes_to_list")),
        Some(&append_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("append_computes_to_list")),
        Some(&append_prop)
    );
    assert_eq!(
        theory.theorem(theorem("append_nil_returns_right")),
        Some(&append_nil_returns_right_prop)
    );
    assert_eq!(
        theory.theorem(theorem("append_right_nil")),
        Some(&append_right_nil_prop)
    );
    assert_eq!(
        theory.theorem(theorem("append_cons")),
        Some(&append_cons_prop)
    );
    assert_eq!(
        theory.theorem(theorem("append_singleton")),
        Some(&append_singleton_prop)
    );
    assert_eq!(
        theory.theorem(theorem("append_assoc")),
        Some(&append_assoc_prop)
    );
    assert_eq!(
        theory
            .known(theorem("reverse_computes_to_list"))
            .expect("reverse theorem should be defined")
            .prop(),
        &reverse_prop,
    );
    assert_eq!(
        checked_theorem("reverse_computes_to_list")
            .expect("reverse theorem source proof should check with dependencies")
            .prop(),
        &reverse_prop,
    );
    assert_eq!(
        checked_theorem("reverse_nil_computes_to_list")
            .expect("reverse nil theorem source proof should check with dependencies")
            .prop(),
        &reverse_nil_prop,
    );
    assert_eq!(
        checked_theorem("reverse_nil")
            .expect("reverse nil exact theorem source proof should check with dependencies")
            .prop(),
        &reverse_nil_exact_prop,
    );
    assert_eq!(
        checked_theorem("reverse_singleton")
            .expect("reverse singleton theorem source proof should check with dependencies")
            .prop(),
        &reverse_singleton_prop,
    );
    assert_eq!(
        checked_theorem("reverse_acc_append")
            .expect("reverse accumulator theorem source proof should check with dependencies")
            .prop(),
        &reverse_acc_append_prop,
    );
    assert_eq!(
        checked_theorem("reverse_cons")
            .expect("reverse cons theorem source proof should check with dependencies")
            .prop(),
        &reverse_cons_prop,
    );
    assert_eq!(
        checked_theorem("reverse_acc_reverse")
            .expect(
                "reverse accumulator inverse theorem source proof should check with dependencies"
            )
            .prop(),
        &reverse_acc_reverse_prop,
    );
    assert_eq!(
        checked_theorem("reverse_double")
            .expect("reverse double theorem source proof should check with dependencies")
            .prop(),
        &reverse_double_prop,
    );
    assert_eq!(
        checked_theorem("reverse_acc_of_append")
            .expect(
                "reverse accumulator append theorem source proof should check with dependencies"
            )
            .prop(),
        &reverse_acc_of_append_prop,
    );
    assert_eq!(
        checked_theorem("reverse_append")
            .expect("reverse append theorem source proof should check with dependencies")
            .prop(),
        &reverse_append_prop,
    );
    assert_eq!(
        checked_theorem("snoc_computes_to_list")
            .expect("snoc theorem source proof should check with dependencies")
            .prop(),
        &snoc_prop,
    );
    assert_eq!(
        checked_theorem("snoc_nil")
            .expect("snoc nil theorem source proof should check with dependencies")
            .prop(),
        &snoc_nil_prop,
    );
    assert_eq!(
        checked_theorem("snoc_cons")
            .expect("snoc cons theorem source proof should check with dependencies")
            .prop(),
        &snoc_cons_prop,
    );
    assert_eq!(
        checked_theorem("concat_nil")
            .expect("concat nil theorem source proof should check with dependencies")
            .prop(),
        &concat_nil_prop,
    );
    assert_eq!(
        checked_theorem("last_nil_errors")
            .expect("last nil theorem source proof should check with dependencies")
            .prop(),
        &last_nil_errors_prop,
    );
    assert_eq!(
        checked_theorem("last_singleton")
            .expect("last singleton theorem source proof should check with dependencies")
            .prop(),
        &last_singleton_prop,
    );
    assert_eq!(
        checked_theorem("last_cons")
            .expect("last cons theorem source proof should check with dependencies")
            .prop(),
        &last_cons_prop,
    );
    assert_eq!(
        checked_theorem("init_nil_errors")
            .expect("init nil theorem source proof should check with dependencies")
            .prop(),
        &init_nil_errors_prop,
    );
    assert_eq!(
        checked_theorem("init_singleton")
            .expect("init singleton theorem source proof should check with dependencies")
            .prop(),
        &init_singleton_prop,
    );
    assert_eq!(
        checked_theorem("init_cons")
            .expect("init cons theorem source proof should check with dependencies")
            .prop(),
        &init_cons_prop,
    );
    assert_eq!(
        checked_theorem("null_nil")
            .expect("null nil theorem source proof should check with dependencies")
            .prop(),
        &null_nil_prop,
    );
    assert_eq!(
        checked_theorem("null_cons")
            .expect("null cons theorem source proof should check with dependencies")
            .prop(),
        &null_cons_prop,
    );
    assert_eq!(
        checked_theorem("is_singleton_nil")
            .expect("is-singleton nil theorem source proof should check with dependencies")
            .prop(),
        &is_singleton_nil_prop,
    );
    assert_eq!(
        checked_theorem("is_singleton_singleton")
            .expect("is-singleton singleton theorem source proof should check with dependencies")
            .prop(),
        &is_singleton_singleton_prop,
    );
    assert_eq!(
        checked_theorem("is_singleton_cons")
            .expect("is-singleton cons theorem source proof should check with dependencies")
            .prop(),
        &is_singleton_cons_prop,
    );
    assert_eq!(
        checked_theorem("append_nil_computes_to_list")
            .expect("append nil theorem source proof should check with dependencies")
            .prop(),
        &append_nil_prop,
    );
    assert_eq!(
        checked_theorem("append_computes_to_list")
            .expect("append theorem source proof should check with dependencies")
            .prop(),
        &append_prop,
    );
    assert_eq!(
        checked_theorem("append_nil_returns_right")
            .expect("append nil exact theorem source proof should check with dependencies")
            .prop(),
        &append_nil_returns_right_prop,
    );
    assert_eq!(
        checked_theorem("append_right_nil")
            .expect("append right nil theorem source proof should check with dependencies")
            .prop(),
        &append_right_nil_prop,
    );
    assert_eq!(
        checked_theorem("append_cons")
            .expect("append cons theorem source proof should check with dependencies")
            .prop(),
        &append_cons_prop,
    );
    assert_eq!(
        checked_theorem("append_singleton")
            .expect("append singleton theorem source proof should check with dependencies")
            .prop(),
        &append_singleton_prop,
    );
    assert_eq!(
        checked_theorem("append_assoc")
            .expect("append associativity theorem source proof should check with dependencies")
            .prop(),
        &append_assoc_prop,
    );
    assert_eq!(
        checked_theorem("map_nil")
            .expect("map nil theorem source proof should check with dependencies")
            .prop(),
        &map_nil_prop,
    );
    assert_eq!(
        checked_theorem("map_cons")
            .expect("map cons theorem source proof should check with dependencies")
            .prop(),
        &map_cons_prop,
    );
    assert_eq!(
        checked_theorem("map_computes_to_list")
            .expect("map computes theorem source proof should check with dependencies")
            .prop(),
        &map_computes_to_list_prop,
    );
    assert_eq!(
        checked_theorem("concat_map_nil")
            .expect("concat-map nil theorem source proof should check with dependencies")
            .prop(),
        &concat_map_nil_prop,
    );
    assert_eq!(
        checked_theorem("concat_map_cons")
            .expect("concat-map cons theorem source proof should check with dependencies")
            .prop(),
        &concat_map_cons_prop,
    );
    assert_eq!(
        checked_theorem("concat_map_computes_to_list")
            .expect("concat-map computes theorem source proof should check with dependencies")
            .prop(),
        &concat_map_computes_to_list_prop,
    );
    assert_eq!(
        checked_theorem("fold_right_nil")
            .expect("fold-right nil theorem source proof should check with dependencies")
            .prop(),
        &fold_right_nil_prop,
    );
    assert_eq!(
        checked_theorem("fold_right_cons")
            .expect("fold-right cons theorem source proof should check with dependencies")
            .prop(),
        &fold_right_cons_prop,
    );
    assert_eq!(
        checked_theorem("fold_right_computes_to_value")
            .expect("fold-right computes theorem source proof should check with dependencies")
            .prop(),
        &fold_right_computes_to_value_prop,
    );
    assert_eq!(
        checked_theorem("fold_left_nil")
            .expect("fold-left nil theorem source proof should check with dependencies")
            .prop(),
        &fold_left_nil_prop,
    );
    assert_eq!(
        checked_theorem("fold_left_cons")
            .expect("fold-left cons theorem source proof should check with dependencies")
            .prop(),
        &fold_left_cons_prop,
    );
    assert_eq!(
        checked_theorem("fold_left_computes_to_value")
            .expect("fold-left computes theorem source proof should check with dependencies")
            .prop(),
        &fold_left_computes_to_value_prop,
    );
    assert_eq!(
        checked_theorem("zip_with_left_nil")
            .expect("zip-with left nil theorem source proof should check with dependencies")
            .prop(),
        &zip_with_left_nil_prop,
    );
    assert_eq!(
        checked_theorem("zip_with_right_nil")
            .expect("zip-with right nil theorem source proof should check with dependencies")
            .prop(),
        &zip_with_right_nil_prop,
    );
    assert_eq!(
        checked_theorem("zip_with_cons")
            .expect("zip-with cons theorem source proof should check with dependencies")
            .prop(),
        &zip_with_cons_prop,
    );
    assert_eq!(
        checked_theorem("zip_with_computes_to_list")
            .expect("zip-with computes theorem source proof should check with dependencies")
            .prop(),
        &zip_with_computes_to_list_prop,
    );
    assert_eq!(
        checked_theorem("filter_nil")
            .expect("filter nil theorem source proof should check with dependencies")
            .prop(),
        &filter_nil_prop,
    );
    assert_eq!(
        checked_theorem("filter_cons_true")
            .expect("filter true cons theorem source proof should check with dependencies")
            .prop(),
        &filter_cons_true_prop,
    );
    assert_eq!(
        checked_theorem("filter_cons_false")
            .expect("filter false cons theorem source proof should check with dependencies")
            .prop(),
        &filter_cons_false_prop,
    );
    assert_eq!(
        checked_theorem("filter_computes_to_list")
            .expect("filter computes theorem source proof should check with dependencies")
            .prop(),
        &filter_computes_to_list_prop,
    );
    assert_eq!(
        checked_theorem("any_nil")
            .expect("any nil theorem source proof should check with dependencies")
            .prop(),
        &any_nil_prop,
    );
    assert_eq!(
        checked_theorem("any_cons_true")
            .expect("any true cons theorem source proof should check with dependencies")
            .prop(),
        &any_cons_true_prop,
    );
    assert_eq!(
        checked_theorem("any_cons_false")
            .expect("any false cons theorem source proof should check with dependencies")
            .prop(),
        &any_cons_false_prop,
    );
    assert_eq!(
        checked_theorem("any_computes_to_bool")
            .expect("any computes theorem source proof should check with dependencies")
            .prop(),
        &any_computes_to_bool_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_true_true")
            .expect("value-eq true theorem source proof should check with dependencies")
            .prop(),
        &value_eq_true_true_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_true_false")
            .expect("value-eq false theorem source proof should check with dependencies")
            .prop(),
        &value_eq_true_false_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_nil")
            .expect("value-eq nil theorem source proof should check with dependencies")
            .prop(),
        &value_eq_nil_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_nil_cons")
            .expect("value-eq nil cons theorem source proof should check with dependencies")
            .prop(),
        &value_eq_nil_cons_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_cons_nil")
            .expect("value-eq cons nil theorem source proof should check with dependencies")
            .prop(),
        &value_eq_cons_nil_prop,
    );
    assert_eq!(
        checked_theorem("value_eq_cons")
            .expect("value-eq cons theorem source proof should check with dependencies")
            .prop(),
        &value_eq_cons_prop,
    );
    assert_eq!(
        checked_theorem("member_nil")
            .expect("member nil theorem source proof should check with dependencies")
            .prop(),
        &member_nil_prop,
    );
    assert_eq!(
        checked_theorem("member_cons_true")
            .expect("member true cons theorem source proof should check with dependencies")
            .prop(),
        &member_cons_true_prop,
    );
    assert_eq!(
        checked_theorem("member_cons_false")
            .expect("member false cons theorem source proof should check with dependencies")
            .prop(),
        &member_cons_false_prop,
    );
    assert_eq!(
        checked_theorem("all_nil")
            .expect("all nil theorem source proof should check with dependencies")
            .prop(),
        &all_nil_prop,
    );
    assert_eq!(
        checked_theorem("all_cons_true")
            .expect("all true cons theorem source proof should check with dependencies")
            .prop(),
        &all_cons_true_prop,
    );
    assert_eq!(
        checked_theorem("all_cons_false")
            .expect("all false cons theorem source proof should check with dependencies")
            .prop(),
        &all_cons_false_prop,
    );
    assert_eq!(
        checked_theorem("all_computes_to_bool")
            .expect("all computes theorem source proof should check with dependencies")
            .prop(),
        &all_computes_to_bool_prop,
    );
    assert_eq!(
        checked_theorem("map_identity")
            .expect("map identity theorem source proof should check with dependencies")
            .prop(),
        &map_identity_prop,
    );
    assert_eq!(
        checked_theorem("concat_map_singleton")
            .expect("concat-map singleton theorem source proof should check with dependencies")
            .prop(),
        &concat_map_singleton_prop,
    );
    assert_eq!(
        checked_theorem("fold_right_cons_nil")
            .expect("fold-right cons theorem source proof should check with dependencies")
            .prop(),
        &fold_right_cons_nil_prop,
    );
    assert_eq!(
        checked_theorem("fold_left_reverse_acc")
            .expect(
                "fold-left reverse accumulator theorem source proof should check with dependencies"
            )
            .prop(),
        &fold_left_reverse_acc_prop,
    );
    assert_eq!(
        checked_theorem("fold_left_reverse")
            .expect("fold-left reverse theorem source proof should check with dependencies")
            .prop(),
        &fold_left_reverse_prop,
    );
}

#[test]
fn prelude_theory_instantiates_named_reverse_theorem() {
    let theory = theory();
    let reverse = theory
        .known(theorem("reverse_computes_to_list"))
        .expect("reverse theorem should be defined");
    let guarded = theory
        .forall_elim(&reverse, list_tests::nil())
        .expect("known theorem should instantiate in its theory");
    let nil_is_list = Theorem::from_proof(
        Proof::Primitive(is_list(list_tests::nil())),
        is_list(list_tests::nil()),
    )
    .expect("nil should prove is-list as a primitive proposition");
    let instantiated = theory
        .implies_elim(&guarded, &nil_is_list)
        .expect("reverse theorem premise should discharge for nil");

    assert_eq!(
        instantiated.prop(),
        &computes_to_list(
            list_tests::reverse_computes_to_list_source_result_symbol(),
            list_tests::reverse_call(list_tests::nil()),
        )
    );
}
