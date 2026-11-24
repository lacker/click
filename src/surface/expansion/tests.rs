use super::*;

// Read proof fixtures at runtime, as the markdown harness does, so editing a
// fixture does not invalidate the Rust test executable.
fn mdtest_markdown(name: &str) -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests")
        .join(name);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()))
}

#[cfg(feature = "fast-gate")]
crate::surface::tests::test_batches! {
    file: "tests.rs",
    marker: "expansion_api_batch_",
    expansion_api_batch_00: [
        nested_match_retains_nominal_list_result,
        generic_list_induction_retains_nominal_pointer_fields,
        retained_caller_expansion_preserves_declared_object_return_evidence,
        grouped_expansion_keeps_postexecution_closers_in_source_order,
    ],
    expansion_api_batch_01: [
        retained_function_expansion_formats_without_reverification_and_rechecks,
        execute_until_in_proof_if_arms_expands_and_rechecks,
        tactic_expansion_can_name_an_outer_c_parameter_after_intro,
        tactic_expansion_can_name_two_levels_of_shadowed_binders,
    ],
    expansion_api_batch_02: [
        integer_function_unfold_expands_and_reverifies,
        nat_integer_laws_expand_and_reject_wrong_successor,
        builtin_nat_integer_dispatch_and_checked_to_nat,
        generic_smart_proofs_expand_without_concrete_clients,
    ],
    expansion_api_batch_03: [
        conditional_normalization_roundtrips_and_rejects_tampering,
        generic_template_expansion_checks_arbitrary_types,
        smart_conditional_normalization_emits_checked_evidence,
        nested_list_membership_expands_and_rechecks,
    ],
    expansion_api_batch_04: [
        scalar_call_congruence_expands_and_rejects_tampering,
        library_list_theorem_application_expands_and_rechecks,
        inventories_and_expands_smart_tactics_inside_structural_induction,
        expands_one_grouped_tactic_without_running_the_suffix,
    ],
    expansion_api_batch_05: [
        expands_grouped_immutable_read_with_multiple_claim_successors,
        expands_nested_branch_tactic_by_source_location,
        source_positions_include_tactics_nested_in_open_blocks,
        expands_common_step_after_frontier_branch,
    ],
    expansion_api_batch_06: [
        expands_deferred_solve_after_frontier_branch,
        shares_equal_deferred_expansions_after_frontier_branch,
        expands_common_deferred_tactic_with_a_returning_branch_arm,
        expands_deferred_solve_after_nested_frontier_branches,
    ],
    expansion_api_batch_07: [
        hides_statement_local_opaque_call_facts_from_surface_premises,
        opaque_call_expansion_keeps_only_consumed_ambient_conditions,
        opaque_call_expansion_keeps_memory_condition_safety,
        expands_public_opaque_call_results_through_later_call_arguments,
    ],
    expansion_api_batch_08: [
        grouped_solve_distinguishes_program_local_result_from_contract_result,
        grouped_solve_expansion_closes_only_the_first_open_claim,
        return_fold_retains_post_return_proof_through_expansion,
        grouped_solve_expansion_preserves_resource_scalar_and_quantified_transitions,
    ],
    expansion_api_batch_09: [
        grouped_solve_expansion_uses_explicit_frame_consequences,
        source_position_maps_implicit_default_proofs,
        expanded_uint8_facts_print_as_parseable_typed_literals,
        expanded_bitvector_facts_print_parseable_negative_literals,
    ],
    expansion_api_batch_10: [
        expanded_branch_condition_names_a_struct_pointer_field,
        expanded_branch_condition_names_a_local_struct_pointer_field,
        expanded_branch_condition_names_a_field_through_a_loaded_pointer,
        expanded_contract_let_facts_remain_source_indexable,
    ],
    expansion_api_batch_11: [
        expanded_post_execution_apply_retains_its_facts_for_the_closer,
        expanded_symbolic_range_propositions_use_parser_syntax,
        expands_single_smart_and_default_function_proofs_by_source_location,
        whole_function_proof_expansion_skips_unrelated_broken_proofs,
    ],
    expansion_api_batch_12: [
        partial_tactic_expansion_skips_unrelated_broken_proofs,
        pure_theorem_expansion_is_certificate_backed_and_idempotent,
        pure_mixed_linear_smart_script_expands_the_retained_proof_object_path,
        pure_branch_local_apply_expands_the_retained_proof_object_paths,
    ],
    expansion_api_batch_13: [
        pure_nested_have_branch_apply_expands_the_retained_proof_object_scope,
        smart_inventory_skips_assumed_extern_contracts,
        smart_inventory_does_not_invent_solve_sites_for_kernel_axiom_declarations,
        smart_inventory_keeps_refinement_proofs_named_like_arithmetic_axioms,
    ],
    expansion_api_batch_14: [
        builtin_nat_integer_laws_expand_and_reject_invalid_conversions,
        nat_addition_agrees_with_integer_addition_and_rechecks_expansion,
        signed_to_unsigned_interval_comparisons_expand_and_recheck_both_sides,
        smart_sites_inside_and_after_cases_and_outcomes_resolve_to_their_source,
    ],
    expansion_api_batch_15: [
        named_applications_are_simple_with_ordinary_obligations,
        commented_selective_and_qualified_names_expand_and_recheck,
        solve_expands_disjunction_projection_to_cases_without_extract,
        solve_expands_propagated_partial_implication_to_known,
    ],
    expansion_api_batch_16: [
        solve_expands_excluded_middle_to_if_without_extract,
        ordinary_fold_expansion_requires_the_empty_range_guard,
        ordinary_fold_expansion_keeps_array_reads_at_the_execution_frontier,
        ordinary_fold_expansion_in_both_replays_without_implicit_solving,
        exact_proposition_propagation_replays_without_search,
    ],
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_00")]
fn nested_match_retains_nominal_list_result() {
    let c = "struct node { int32 value; }; struct other { int32 value; };
        int32 member(struct node* node) { return 1; }";
    let source = r#"
verifying "node.c";
spec enum Nodes { Empty, Link(struct node*, Nodes) }
function keep_node(node: struct node*) -> struct node* { node }
function singleton(node: struct node*) -> List<struct node*> {
    List::Cons(node, List::Nil)
}
function singleton_return(node: struct node*) -> List<struct node*> {
    List::Cons(keep_node(node), List::Nil)
}
function singleton_contains(node: struct node*) -> Bool {
    list::contains(singleton(node), node)
}
function singleton_contains_return(node: struct node*) -> Bool {
    list::contains(singleton(node), keep_node(node))
}
predicate typed_contains(nodes: List<struct node*>, node: struct node*) {
    list::contains(nodes, node)
}
int32 member(struct node* node) {
    requires list::contains(singleton(node), node);
    requires list::contains(List::Cons(node, List::Nil), node);
    ensures result == 1;
}
function first(nodes: Nodes) -> List<struct node*> decreases nodes {
    match nodes {
        Nodes::Empty => List::Nil,
        Nodes::Link(node, tail) => match tail {
            Nodes::Empty => List::Cons(node, List::Nil),
            Nodes::Link(next, rest) => first(tail),
        },
    }
}
theorem first_null() {
    ensures first(Nodes::Link(0, Nodes::Empty))
        == List<struct node*>::Cons(0, List<struct node*>::Nil) by {
            unfold(first(Nodes::Link(0, Nodes::Empty)));
            normalize();
        }
}
theorem singleton_null() {
    ensures singleton(0) == List<struct node*>::Cons(0, List<struct node*>::Nil)
        by { unfold(singleton(0)); normalize(); }
}
theorem singleton_return_null() {
    ensures singleton_return(0) == List<struct node*>::Cons(0, List<struct node*>::Nil)
        by { unfold(singleton_return(0)); unfold(keep_node(0)); normalize(); }
}
theorem typed_membership(xs: List<struct node*>, target: struct node*) {
    ensures list::contains(xs, target) == list::contains(xs, target)
        by { normalize(); }
}
"#;
    verify_c_sources(source, &[("node.c", c)])
        .unwrap_or_else(|error| panic!("{}", error.message()));
    for field_type in ["int32*", "struct other*"] {
        let wrong = source.replace(
            "Link(struct node*, Nodes)",
            &format!("Link({field_type}, Nodes)"),
        );
        let error = verify_c_sources(&wrong, &[("node.c", c)])
            .expect_err("a matched payload must retain its own declared class");
        assert!(
            error.message().contains("function `first`"),
            "{}",
            error.message()
        );
        let wrong = source.replace("target: struct node*", &format!("target: {field_type}"));
        let error = verify_c_sources(&wrong, &[("node.c", c)])
            .expect_err("a bool result does not remove its arguments' nominal requirements");
        assert!(
            error.message().contains("cannot infer type arguments")
                || error.message().contains("requires original object class"),
            "{}",
            error.message()
        );
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_00")]
fn generic_list_induction_retains_nominal_pointer_fields() {
    let c = "struct node { int32 value; }; struct other { int32 value; };";
    let source = r#"
verifying "node.c";
function retain<T>(value: T) -> T { value }
theorem null_has_nominal_list_type() {
    ensures List<struct node*>::Cons(0, List<struct node*>::Nil)
        == List<struct node*>::Cons(0, List<struct node*>::Nil) by { normalize(); }
}
theorem typed_head(head: struct node*) {
    ensures head == head by { normalize(); }
}
theorem typed_tail(items: List<struct node*>) {
    ensures 0 == 0 by { normalize(); }
}
theorem list_has_typed_heads(xs: List<struct node*>) {
    ensures 0 == 0 by {
        let ih = induct(xs);
        match xs {
            List::Nil => { normalize(); }
            List::Cons(head, tail) => {
                apply(typed_head(head));
                apply(typed_head(retain(head)));
                apply(typed_tail(tail));
                apply(list::append_cons(head, tail, tail));
                apply(list::append_cons(head as (void *), List<void*>::Nil, List<void*>::Nil));
                apply(list::append_cons(head as (int32 *), List<int32*>::Nil, List<int32*>::Nil));
                apply(list::append_cons(retain(head as (void *)), List<void*>::Nil, List<void*>::Nil));
                apply(list::append_cons(retain(head as (int32 *)), List<int32*>::Nil, List<int32*>::Nil));
                normalize();
            }
        }
    }
}
"#;
    verify_c_sources(source, &[("node.c", c)])
        .unwrap_or_else(|error| panic!("{}", error.message()));
    for element in ["int32*", "struct other*"] {
        let wrong = source.replace("List<struct node*>", &format!("List<{element}>"));
        let error = verify_c_sources(&wrong, &[("node.c", c)])
            .expect_err("an untyped or differently typed payload cannot acquire node's class");
        assert!(
            error
                .message()
                .contains("requires original object class `struct node`"),
            "{}",
            error.message()
        );
    }
}

#[test]
fn callback_refinement_preserves_generated_address_obligations() {
    let path = std::path::Path::new("rb_augment_callbacks_const_suite.md");
    let fixture = crate::cli::parse_mdtest(
        path,
        &mdtest_markdown("rb_augment_callbacks_const_suite.md"),
    )
    .unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c_sources(source, &sources).unwrap_or_else(|error| panic!("{}", error.message()));
    let incompatible = source.replacen(
        "ensures node->left == old(node->left);",
        "ensures node->left != old(node->left);",
        1,
    );
    let error = verify_c_sources(&incompatible, &sources)
        .expect_err("a no-op callback cannot refine the incompatible named guarantee");
    assert!(
        error
            .message()
            .contains("dummy_propagate_contract.ensures_0"),
        "{}",
        error.message()
    );
}

#[test]
fn aggregate_leaf_resources_retain_enclosing_subobject_bounds() {
    let path = std::path::Path::new("struct_aggregate_resources.md");
    let fixture =
        crate::cli::parse_mdtest(path, &mdtest_markdown("struct_aggregate_resources.md")).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c_sources_functions(source, &sources, ["read_inner".to_string()])
        .unwrap_or_else(|error| panic!("{}", error.message()));
    let changed =
        fixture.c_sources[0]
            .1
            .replacen("return packet->inner.count;", "return packet->tail;", 1);
    let error = verify_c_sources_functions(
        source,
        &[(fixture.c_sources[0].0.as_str(), changed.as_str())],
        ["read_inner".to_string()],
    )
    .expect_err("the enclosing member's bounds do not authorize the following field");
    assert!(
        error
            .message()
            .contains("access outside the subobject the pointer designates"),
        "{}",
        error.message()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_00")]
fn retained_caller_expansion_preserves_declared_object_return_evidence() {
    let path = std::path::Path::new("model_pointer_c_returns_keep_declared_object_evidence.md");
    let fixture = crate::cli::parse_mdtest(
        path,
        &mdtest_markdown("model_pointer_c_returns_keep_declared_object_evidence.md"),
    )
    .unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let (session, verified) = ProgramVerificationSession::new(source, &sources).unwrap();
    let expanded =
        expand_verified_function_claim_source_by_label(source, &verified, "caller.contract")
            .unwrap()
            .unwrap();
    let position = c_tactic_source_position(&expanded, &sources, "caller.contract", 0).unwrap();
    without_implicit_solve(|| session.verify_at(&expanded, position.line, position.column))
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
    crate::surface::without_implicit_solve_for_claim("caller.contract", || {
        verify_c_sources(&expanded, &sources).map_err(|error| error.report())
    })
    .unwrap();
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_00")]
fn grouped_expansion_keeps_postexecution_closers_in_source_order() {
    let path = std::path::Path::new("solve_after_execution_acts_on_the_first_open_claim.md");
    let fixture = crate::cli::parse_mdtest(
        path,
        &mdtest_markdown("solve_after_execution_acts_on_the_first_open_claim.md"),
    )
    .unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let (_session, verified) = ProgramVerificationSession::new(source, &sources).unwrap();
    let expanded = expand_verified_function_claim_source_by_label(source, &verified, "f.contract")
        .unwrap()
        .unwrap();
    without_implicit_solve(|| verify_c_sources(&expanded, &sources))
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

#[test]
fn project_claim_expansion_retains_imported_resources() {
    let source = r#"
import "cell.click";
verifying "skip.c";
int32 skip(int32* p) {
    owns cell(p);
    ensures result == 0;
}
"#;
    let project = ClickProject::new(
        "skip.click",
        [
            ClickModuleSource::new("skip.click", source, ["cell.click".to_string()]),
            ClickModuleSource::new("cell.click", "resource cell(p: int32*) { owns *p; }", []),
        ],
    );
    let sources = [("skip.c", "int32 skip(int32* p) { return 0; }")];
    verify_c_project(&project, &sources).expect("the imported resource contract verifies");
    let expanded = expand_project_claim_source_by_label(
        &project,
        &ProgramInputs::Bundle(sources.to_vec()),
        "skip.contract",
    )
    .expect("validation must retain the imported resource declaration");
    verify_c_project(&project.with_entry_source(expanded), &sources)
        .expect("the expanded imported-resource proof must reverify");
}

// Audit may format the certificate its session already checked, but the
// rewrite still needs independent verification against the actual program.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_01")]
fn retained_function_expansion_formats_without_reverification_and_rechecks() {
    let c = "int32 id(int32 x) { return x; }";
    let source = "verifying \"id.c\"; int32 id(int32 x) { ensures result == x; }";
    let (_session, verified) = ProgramVerificationSession::new(source, &[("id.c", c)]).unwrap();
    let (rewritten, events) = instrumentation::collect(|| {
        expand_verified_function_claim_source_by_label(source, &verified, "id.ensures_0")
            .unwrap()
            .unwrap()
    });
    assert!(
        !events
            .iter()
            .any(|event| matches!(event, instrumentation::VerificationEvent::TacticStarted(_)))
    );
    assert_eq!(
        rewritten,
        expand_c_claim_source_by_label(source, &[("id.c", c)], "id.ensures_0").unwrap()
    );
    verify_c_sources(&rewritten, &[("id.c", c)]).unwrap();
    assert!(verify_c_sources(&rewritten, &[("id.c", "int32 id(int32 x) { return 0; }")]).is_err());
}

#[test]
fn batch_source_positions_preserve_unicode_columns_and_request_order() {
    let source = "αβ;\n\tγδ;\nlast";
    let offsets = [source.len(), 2, 0, 9, 2];
    assert_eq!(
        positions_at_offsets(source, offsets),
        offsets.map(|offset| position_at_offset(source, offset))
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_01")]
fn execute_until_in_proof_if_arms_expands_and_rechecks() {
    let c = "int32 identity(int32 x) { int32 y = x; return y; }";
    let source = r#"
verifying "identity.c";
int32 identity(int32 x) { ensures result == x; } by {
    if x == 0 {
        step_until(region(0).entry);
        step_until(assignment(y, 0).entry);
        step(); step_until(function.exit); close();
    } else {
        step_until(region(0).entry);
        step_until(assignment(y, 0).entry);
        step(); step_until(function.exit); close();
    }
}
"#;
    let sources = [("identity.c", c)];
    verify_c_sources(source, &sources).unwrap();
    let expanded = expand_c_claim_source_by_label(source, &sources, "identity.contract").unwrap();
    verify_c_sources(&expanded, &sources).unwrap();
    assert!(
        verify_c_sources(
            &expanded.replace("ensures result == x;", "ensures result == x + 1;"),
            &sources,
        )
        .is_err()
    );
}

/// `rb_erase`'s general wrapper (`examples/rbtree/rbtree-erase`): a file-static
/// callbacks struct is folded and passed to a call whose outcome resource
/// unfolds into a child named like the contract's own `produces whole`.
/// `step_until(function.exit); close();` expands to `have whole.model == ...`, which reads
/// the unfolded child through the contract binder's resource, not the
/// outcome resource the unfold named it from.
#[test]
fn unfolded_child_named_like_a_produced_binder_expands_and_rechecks() {
    let c = r#"
struct root { int value; };
struct callbacks { void (*rotate)(struct root *); };

static void dummy_rotate(struct root *root) {}

static const struct callbacks dummy_callbacks = {
    .rotate = dummy_rotate
};

int produce(struct root *root, const struct callbacks *augment) {
    return 0;
}

void use(struct root *root) {
    int r;
    r = produce(root, &dummy_callbacks);
}
"#;
    let source = r#"
verifying "callbacks_outcome.c";

spec enum Out {
    Done(int32),
    Pending(int32),
}

function out_value(o: Out) -> int32 {
    match o {
        Out::Done(v) => v,
        Out::Pending(v) => v,
    }
}

resource cell_at(p: struct root*) {
    field model: int32;
    owns p->value;
    fact p->value == model;
}

resource out_at(p: struct root*, r: int32) {
    field model: Out;
    match model {
        Out::Done(v) => {
            owns whole: cell_at(p);
            fact whole.model == v;
            fact r == 0;
        },
        Out::Pending(v) => {
            owns pending: cell_at(p);
            fact pending.model == v;
            fact r != 0;
        },
    }
}

contract void Rotate(struct root* root) {
    ensures 1 == 1;
}

resource callbacks_at(augment: const struct callbacks*) {
    views augment->rotate;
    fact Rotate(augment->rotate);
}

void dummy_rotate(struct root* root) {
    ensures 1 == 1;
} by { step_until(function.exit); normalize(); }

theorem dummy_rotate_contract() {
    ensures Rotate(&dummy_rotate) by { unfold(Rotate(&dummy_rotate)); close(); }
}

int produce(struct root* root, const struct callbacks* augment) {
    consumes cell: cell_at(root);
    views callbacks_at(augment);
    produces out: out_at(root, result);
    ensures out_value(out.model) == old(cell.model);
} by {
    step_until(function.exit);
    let out = fold(out_at(root, 0), { model: Out::Done(cell.model), whole: cell });
    close();
}

void use(struct root* root) {
    consumes cell: cell_at(root);
    views dummy_callbacks.rotate;
    produces whole: cell_at(root);
    ensures whole.model == old(cell.model);
} by {
    apply(dummy_rotate_contract());
    fold(callbacks_at(&dummy_callbacks));
    step();
    let { out: out } = step(produce, { cell: cell });
    match out.model {
        Out::Done(v) => {
            have out_value(Out::Done(v)) == old(cell.model) by { rewrite(Out::Done(v), out.model); close(); }
            have v == old(cell.model) by { unfold(out_value(Out::Done(v))); close(); }
            let { whole: whole } = unfold(out);
            step_until(function.exit); close();
        },
        Out::Pending(v) => {
            have out_value(Out::Pending(v)) == old(cell.model) by { rewrite(Out::Pending(v), out.model); close(); }
            have v == old(cell.model) by { unfold(out_value(Out::Pending(v))); close(); }
            let { pending: whole } = unfold(out);
            step_until(function.exit); close();
        },
    }
}
"#;
    let sources = [("callbacks_outcome.c", c)];
    verify_c_sources(source, &sources).unwrap();
    let expanded = expand_c_claim_source_by_label(source, &sources, "use.contract").unwrap();
    assert!(
        expanded.contains("have whole.model == old(cell.model) by"),
        "the expansion should read the unfolded child through the produced binder: {expanded}"
    );
    crate::surface::proof::without_implicit_solve_for_claim("use.contract", || {
        verify_c_sources(&expanded, &sources).map_err(|error| error.report())
    })
    .unwrap();
    assert!(
        crate::surface::proof::without_implicit_solve_for_claim("use.contract", || {
            verify_c_sources(
                &expanded.replace(
                    "ensures whole.model == old(cell.model);",
                    "ensures whole.model == old(cell.model) + 1;",
                ),
                &sources,
            )
            .map_err(|error| error.report())
        })
        .is_err()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_01")]
fn tactic_expansion_can_name_an_outer_c_parameter_after_intro() {
    let c_source = "int32 shadowed_c(int32 x) { return 0; }";
    let click_source = r#"
verifying "shadowed.c";

int32 shadowed_c(int32 x) {
    requires x == 0;
    ensures forall (x: int32) { x == x };
} by {
    step_until(function.exit);
    intro();
    have outer.x == 0 by { close(); }
    close();
}
"#;
    let sources = [("shadowed.c", c_source)];
    verify_c_sources(click_source, &sources).expect("C proof should retain the outer x");
    let position = position_at_offset(click_source, click_source.find("close();").unwrap());
    let expanded =
        expand_c_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("selected smart tactic should expand");
    assert!(
        expanded.contains("have outer.x == 0 by { close(); }"),
        "{expanded}"
    );
    assert!(expanded.contains("outer.x"), "{expanded}");
    verify_c_sources(&expanded, &sources).expect("expanded C proof must reverify");

    let wrong_binder = click_source.replace("have outer.x == 0", "have x == 0");
    verify_c_sources(&wrong_binder, &sources)
        .expect_err("the fresh universal x must not inherit the parameter's equality");
}

#[test]
fn tactic_expansion_can_name_two_outer_program_binders_after_intro() {
    let c_source = "int32 shadowed_twice_c(int32 x) { return 0; }";
    let click_source = r#"
verifying "shadowed.c";

int32 shadowed_twice_c(int32 x) {
    requires x == 0;
    ensures forall (x: int32) { forall (x: int32) { x == x } };
} by {
    step_until(function.exit);
    intro();
    intro();
    have outer.outer.x == 0 by { close(); }
    close();
}
"#;
    let sources = [("shadowed.c", c_source)];
    verify_c_sources(click_source, &sources).expect("both shadowed binders stay distinct");
    let position = position_at_offset(click_source, click_source.find("close();").unwrap());
    let expanded =
        expand_c_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("selected smart tactic should expand");
    assert!(
        expanded.contains("have outer.outer.x == 0 by { close(); }"),
        "{expanded}"
    );
    verify_c_sources(&expanded, &sources).expect("expanded nested C proof must reverify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_01")]
fn tactic_expansion_can_name_two_levels_of_shadowed_binders() {
    let source = r#"
theorem shadowed_twice(x: int32) {
    requires x == 0;
    ensures forall (x: int32) { forall (x: int32) { x == x } } by {
        intro();
        intro();
        have outer.outer.x == 0 by { close(); }
        close();
    }
}
"#;
    verify_c_sources(source, &[]).expect("the oldest x should remain available");
    let position = position_at_offset(source, source.find("close();").unwrap());
    let expanded = expand_c_tactic_source_at(source, &[], position.line, position.column)
        .expect("selected smart tactic should expand");
    assert!(!expanded.contains("solve();"), "{expanded}");
    assert!(expanded.contains("close();"), "{expanded}");
    assert!(expanded.contains("outer.outer.x"), "{expanded}");
    verify_c_sources(&expanded, &[]).expect("expanded proof must reverify");

    let wrong_depth = source.replace("outer.outer.x", "outer.outer.outer.x");
    verify_c_sources(&wrong_depth, &[])
        .expect_err("a qualifier beyond the enclosing x bindings must fail");
}

#[test]
fn tactic_line_disambiguation_uses_columns_only_for_shared_lines() {
    let multiple = |source: &str, position: &SourcePosition| {
        ProofSourceIndex::new(source)
            .unwrap()
            .line_has_multiple_starts(position)
            .unwrap()
    };
    let source = "void f() {} by { step(); step(); }\nvoid g() {} by {\n    step();\n}\n";
    let steps = source
        .match_indices("step")
        .map(|(offset, _)| position_at_offset(source, offset))
        .collect::<Vec<_>>();
    assert!(multiple(source, &steps[0]));
    assert!(multiple(source, &steps[1]));
    assert!(!multiple(source, &steps[2]));

    let quantified = "theorem t() { ensures true by { have exists (x: int32) { x == x }; } }\n";
    let have = position_at_offset(quantified, quantified.find("have").unwrap());
    assert!(!multiple(quantified, &have));

    let nested = "theorem t(n: int32) { ensures true by {\n    have n <= n by { close(); }\n} }\n";
    let have = position_at_offset(nested, nested.find("have").unwrap());
    let solve = position_at_offset(nested, nested.find("close").unwrap());
    assert!(!multiple(nested, &have));
    assert!(multiple(nested, &solve));
}

#[test]
fn trace_target_selects_only_the_arm_containing_its_source_position() {
    let source =
        "void f() {} by {\n  branch { false => { step(); }, true => { step(); } }\n  step();\n}\n";
    let branch = position_at_offset(source, source.find("branch").unwrap());
    let then_step = position_at_offset(
        source,
        source.find("true => { step").unwrap() + "true => { ".len(),
    );
    let else_step = position_at_offset(
        source,
        source.find("false => { step").unwrap() + "false => { ".len(),
    );
    let continuation = position_at_offset(source, source.rfind("step();").unwrap());
    let index = ProofSourceIndex::new(source).unwrap();
    assert_eq!(index.arm_containing(&branch, &then_step).unwrap(), Some(0));
    assert_eq!(index.arm_containing(&branch, &else_step).unwrap(), Some(1));
    assert_eq!(index.arm_containing(&branch, &continuation).unwrap(), None);
}

#[test]
fn nested_tactic_position_follows_have_and_open_bodies() {
    let source = "resource cell(p: int32*) { owns *p; }\nvoid f(int32* p) {\n    owns r: cell(p);\n} by {\nhave true by {\n    with(cell(p)) {\n        have true by {\n            close();\n        }\n    }\n}\n}\n";
    let have = position_at_offset(source, source.find("have").unwrap());
    let position = ProofSourceIndex::new(source)
        .unwrap()
        .nested_position(&have, &[0, 0, 0])
        .expect("nested step has a source position");
    assert_eq!(
        position,
        position_at_offset(source, source.find("close").unwrap())
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_02")]
fn integer_function_unfold_expands_and_reverifies() {
    let source = r#"
function successor(z: Integer) -> Integer {
    z + 1
}

theorem successor_expansion(z: Integer) {
    ensures successor(z) == z + 1 by {
        unfold(successor(z));
        close();
    }
}
"#;
    verify_c_sources(source, &[]).expect("Integer successor source verifies");
    let expanded = expand_c_claim_source_by_label(source, &[], "successor_expansion.ensures_0")
        .expect("Integer successor claim expands");
    verify_c_sources(&expanded, &[]).expect("expanded Integer successor re-verifies");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_02")]
fn nat_integer_laws_expand_and_reject_wrong_successor() {
    let source = r#"
theorem nat_integer_client(n: Nat) {
    ensures to_integer(Nat::Succ(n)) == to_integer(n) + 1 by {
        apply(nat::to_integer_succ(n));
    }
}
"#;
    verify_c_sources(source, &[]).expect("Nat conversion law verifies");
    let expanded = expand_c_claim_source_by_label(source, &[], "nat_integer_client.ensures_0")
        .expect("Nat conversion claim expands");
    verify_c_sources(&expanded, &[]).expect("expanded Nat conversion re-verifies");

    let invalid = source.replace("+ 1", "+ 2");
    assert!(verify_c_sources(&invalid, &[]).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_02")]
fn builtin_nat_integer_dispatch_and_checked_to_nat() {
    let source = r#"
theorem nat_dispatch(n: Nat) {
    ensures to_integer(n) == to_integer(n) by { normalize(); }
}
theorem checked_to_nat(z: Integer) {
    requires z >= 0;
    ensures to_nat(z) == to_nat(z) by { normalize(); }
}
"#;
    verify_c_sources(source, &[]).expect("Nat/Integer conversion dispatch verifies");
    let missing_bound = r#"
theorem missing_to_nat_bound(z: Integer) {
    ensures to_nat(z) == to_nat(z) by { normalize(); }
}
"#;
    assert!(verify_c_sources(missing_bound, &[]).is_err());
    let nested_missing_bound = r#"
theorem nested_missing_to_nat_bound(z: Integer) {
    ensures Nat::Succ(to_nat(z)) == Nat::Succ(to_nat(z)) by { normalize(); }
}
"#;
    assert!(verify_c_sources(nested_missing_bound, &[]).is_err());
    let shadowed = r#"
function to_nat(z: Integer) -> Nat { Nat::Zero }
"#;
    assert!(verify_c_sources(shadowed, &[]).is_err());
}

#[test]
fn successive_constructor_unfolds_retain_a_checked_goal() {
    let source = r#"
theorem add_two(n: Nat) {
    ensures nat::add(Nat::Succ(Nat::Succ(Nat::Zero)), n) == Nat::Succ(Nat::Succ(n)) by {
        unfold(nat::add(Nat::Succ(Nat::Succ(Nat::Zero)), n));
        unfold(nat::add(Nat::Succ(Nat::Zero), n));
        unfold(nat::add(Nat::Zero, n));
        normalize();
    }
}
theorem singleton<T>(x: T) {
    ensures list::length(List<T>::Cons(x, List<T>::Nil)) == Nat::Succ(Nat::Zero) by {
        unfold(list::length(List<T>::Cons(x, List<T>::Nil)));
        unfold(list::length(List<T>::Nil));
        normalize();
    }
}
"#;
    verify_c_sources(source, &[]).expect("successive explicit unfolds verify");
    let smart_source = source.replace("normalize();", "close();");
    verify_c_sources(&smart_source, &[]).expect("smart closers have checked certificates");
    for (claim, index) in [("add_two.ensures_0", 3), ("singleton.ensures_0", 2)] {
        let position = c_tactic_source_position(&smart_source, &[], claim, index).unwrap();
        let expanded =
            expand_c_tactic_source_at(&smart_source, &[], position.line, position.column).unwrap();
        verify_c_sources(&expanded, &[]).expect("successive unfolds expand and recheck");
    }
    let tampered = source.replace("== Nat::Succ(Nat::Succ(n))", "== Nat::Succ(n)");
    assert!(verify_c_sources(&tampered, &[]).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_02")]
fn generic_smart_proofs_expand_without_concrete_clients() {
    let source = r#"
theorem independent<T, U>(x: T, y: U) {
    ensures x == x by { close(); }
    ensures y == y by { close(); }
}
theorem lists<T>(xs: List<List<T>>) {
    ensures list::append(xs, List<List<T>>::Nil) == xs by {
        apply(list::append_right_identity(xs));
    }
}
"#;
    let verified = verify_click_theorems(source).expect("parametric proofs verify");
    assert_eq!(verified.len(), 3);
    for claim in [
        "independent.ensures_0",
        "independent.ensures_1",
        "lists.ensures_0",
    ] {
        let position = c_tactic_source_position(source, &[], claim, 0).unwrap();
        let expanded =
            expand_c_tactic_source_at(source, &[], position.line, position.column).unwrap();
        assert!(expanded.contains("independent<T, U>"));
        assert!(expanded.contains("lists<T>"));
        verify_c_sources(&expanded, &[]).expect("expanded parametric certificate rechecks");
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_03")]
fn conditional_normalization_roundtrips_and_rejects_tampering() {
    let source = r#"
theorem client(xs: List<int32>, ys: List<int32>) {
    requires not(xs == ys);
    ensures (if xs == ys { 1 } else { 0 }) == 0 by {
        normalize() using { not(xs == ys); }
    }
}
"#;
    verify_c_sources(source, &[]).expect("conditional client verifies before expansion");
    let position = c_tactic_source_position(source, &[], "client.ensures_0", 0).unwrap();
    let expanded = expand_c_tactic_source_at(source, &[], position.line, position.column)
        .expect("simple conditional normalization roundtrips");
    assert!(expanded.contains("normalize() using"));
    verify_c_sources(&expanded, &[]).expect("conditional certificate rechecks");
    for tampered in [
        expanded.replace("requires not(xs == ys);", "requires xs == ys;"),
        expanded.replace("not(xs == ys)", "xs == ys"),
        expanded.replace("else { 0 }) == 0", "else { 0 }) == 1"),
    ] {
        assert_ne!(tampered, expanded);
        assert!(verify_c_sources(&tampered, &[]).is_err());
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_03")]
fn generic_template_expansion_checks_arbitrary_types() {
    let source = r#"
theorem client<T>(xs: List<T>, ys: List<T>) {
    requires not(xs == ys);
    ensures (if xs == ys { 1 } else { 0 }) == 0 by {
        normalize() using { not(xs == ys); }
    }
}
"#;
    let position = c_tactic_source_position(source, &[], "client.ensures_0", 0)
        .expect("generic parameter lists have source locations");
    let expanded = expand_c_tactic_source_at(source, &[], position.line, position.column)
        .expect("a template has a checked parametric certificate");
    verify_c_sources(&expanded, &[]).expect("expanded template rechecks without a client");
    assert!(
        verify_c_sources(
            &expanded.replace("requires not(xs == ys);", "requires xs == ys;"),
            &[]
        )
        .is_err()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_03")]
fn smart_conditional_normalization_emits_checked_evidence() {
    let source = r#"
function same_list(xs: List<int32>, ys: List<int32>) -> int32 {
    if xs == ys { 1 } else { 0 }
}
theorem client(xs: List<int32>, ys: List<int32>) {
    requires not(xs == ys);
    ensures same_list(xs, ys) == 0 by { close(); }
}
"#;
    verify_c_sources(source, &[]).expect("smart conditional proof verifies");
    let position = c_tactic_source_position(source, &[], "client.ensures_0", 0).unwrap();
    let expanded = expand_c_tactic_source_at(source, &[], position.line, position.column)
        .expect("smart conditional proof expands");
    assert!(expanded.contains("close();"), "{expanded}");
    assert!(!expanded.contains("normalize()"), "{expanded}");
    verify_c_sources(&expanded, &[]).expect("emitted conditional evidence rechecks");
    assert!(
        verify_c_sources(
            &expanded.replace("requires not(xs == ys);", "requires xs == ys;"),
            &[],
        )
        .is_err()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_03")]
fn nested_list_membership_expands_and_rechecks() {
    let source = r#"
theorem client(xs: List<List<int32>>, ys: List<List<int32>>, value: List<int32>) {
    ensures list::contains(list::append(xs, ys), value)
        == if list::contains(xs, value) { true } else { list::contains(ys, value) } by {
        apply(list::contains_append(xs, ys, value));
    }
}
"#;
    verify_c_sources(source, &[]).expect("nested-list client verifies before expansion");
    let position = c_tactic_source_position(source, &[], "client.ensures_0", 0).unwrap();
    let expanded = expand_c_tactic_source_at(source, &[], position.line, position.column)
        .expect("nested-list application expands");
    verify_c_sources(&expanded, &[]).expect("expanded nested-list client rechecks");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_04")]
fn scalar_call_congruence_expands_and_rejects_tampering() {
    let source = r#"
theorem client(xs: List<int32>, ys: List<int32>, value: int32) {
    requires xs == ys;
    ensures list::contains(xs, value) == list::contains(ys, value) by {
        rewrite(xs, ys);
        close();
    }
}
"#;
    verify_c_sources(source, &[]).expect("rewrite client verifies before expansion");
    let position = c_tactic_source_position(source, &[], "client.ensures_0", 1).unwrap();
    let expanded = expand_c_tactic_source_at(source, &[], position.line, position.column)
        .expect("rewritten scalar goal expands");
    verify_c_sources(&expanded, &[]).expect("expanded rewrite client rechecks");
    let tampered = expanded.replace("requires xs == ys;", "requires xs == xs;");
    assert!(verify_c_sources(&tampered, &[]).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_04")]
fn library_list_theorem_application_expands_and_rechecks() {
    let source = r#"
theorem client(xs: List<int32>, ys: List<int32>, zs: List<int32>) {
    ensures list::append(list::append(xs, ys), zs) == list::append(xs, list::append(ys, zs)) by {
        apply(list::append_associative(xs, ys, zs));
    }
}
"#;
    verify_c_sources(source, &[]).expect("library client verifies before expansion");
    let position = c_tactic_source_position(source, &[], "client.ensures_0", 0)
        .expect("application has a source position");
    let expanded = expand_c_tactic_source_at(source, &[], position.line, position.column)
        .expect("library theorem application expands");
    verify_c_sources(&expanded, &[]).expect("expanded library client rechecks");
}

#[test]
fn expansion_spells_qualified_module_citations_by_their_in_scope_path() {
    let source = "import click::integer;\ntheorem client() {}\n";
    assert_eq!(
        printing::spell_source_names(
            source,
            "apply(click::list::append_cons(x, xs, ys)); \
             apply(click::integer::multiply_add(x));"
        ),
        "apply(list::append_cons(x, xs, ys)); apply(integer::multiply_add(x));"
    );
    let shadowing = "theorem append_cons() {}\n";
    assert_eq!(
        printing::spell_source_names(shadowing, "apply(click::list::append_cons(x, xs, ys));"),
        "apply(list::append_cons(x, xs, ys));"
    );
    let selective = "import click::list::{append, append_cons};\n";
    assert_eq!(
        printing::spell_source_names(selective, "apply(click::list::append_cons(x, xs, ys));"),
        "apply(append_cons(x, xs, ys));"
    );
}

#[test]
fn expansion_keeps_explicit_library_paths_and_unimported_predicates() {
    let source = "theorem client() { ensures click::bytes::equal(p, 0, q, 0, 1) by close(); }";
    assert_eq!(
        printing::spell_source_names(source, "have click::bytes::equal(p, 0, q, 0, 1);"),
        "have click::bytes::equal(p, 0, q, 0, 1);"
    );
    assert_eq!(
        printing::spell_source_names(
            "theorem client() {}",
            "have click::bytes::equal(p, 0, q, 0, 1);"
        ),
        "have click::bytes::equal(p, 0, q, 0, 1);"
    );
    assert_eq!(
        printing::spell_source_names(
            "/* import click::bytes; */ theorem client() {}",
            "have click::bytes::equal(p, 0, q, 0, 1);"
        ),
        "have click::bytes::equal(p, 0, q, 0, 1);"
    );
    assert_eq!(
        printing::spell_source_names(
            "import click::bytes;",
            "have click::bytes::equal(p, 0, q, 0, 1);"
        ),
        "have bytes::equal(p, 0, q, 0, 1);"
    );
    assert_eq!(
        printing::spell_source_names(
            "apply(click::list::append_left_identity(xs));",
            "apply(click::list::append_left_identity(xs));"
        ),
        "apply(click::list::append_left_identity(xs));"
    );
}

#[test]
fn block_tactic_optional_semicolon_belongs_to_the_tactic() {
    let source = "theorem t() {\n    ensures true by { step(); close(); }\n}\n";
    let file = parser::parse_file_items(source).expect("source should parse");
    let tokens = proof_source_tokens(source, &file.source_spans().implicit_proofs)
        .expect("source should tokenize");
    let tokens = ProofTokens::new(&file, &tokens);
    let by = tokens
        .iter()
        .position(|token| token.text == "by")
        .expect("proof should contain by");
    let open = by + 1;
    let close = tokens
        .block_close(open)
        .expect("proof block should have a closing brace");
    let ranges = tokens
        .tactic_ranges(open, close)
        .expect("block tactics should be indexable");

    assert_eq!(ranges.len(), 2, "{ranges:?}");
    assert_eq!(tokens[ranges[0].end - 1].text, ";");
    assert_eq!(tokens[ranges[1].end - 1].text, ";");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_04")]
fn inventories_and_expands_smart_tactics_inside_structural_induction() {
    let click_source = r#"
spec enum TestList<T> {
    Nil,
    Cons(T, TestList<T>),
}

theorem reflexive(xs: TestList<int32>) {
    ensures xs == xs by {
        let ih = induct(xs);
        match xs {
            TestList::Nil => {
                close();
            }
            TestList::Cons(head, tail) => {
                close();
            }
        }
    }
}
"#;
    let sites = c_smart_tactic_source_sites(click_source, &[])
        .expect("structural induction sites should be indexed");
    assert_eq!(
        sites,
        vec![
            SmartTacticSourceSite {
                claim_label: "reflexive.ensures_0".to_string(),
                source_index: 2,
                tactic_name: "close".to_string(),
                position: position_at_offset(click_source, click_source.find("close();").unwrap()),
            },
            SmartTacticSourceSite {
                claim_label: "reflexive.ensures_0".to_string(),
                source_index: 3,
                tactic_name: "close".to_string(),
                position: position_at_offset(click_source, click_source.rfind("close();").unwrap()),
            },
        ]
    );
    let position = c_tactic_source_position(click_source, &[], "reflexive.ensures_0", 2)
        .expect("the first induction arm should have a source position");
    let expanded = expand_c_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("a smart tactic in an induction arm should expand");
    assert!(expanded.contains("TestList::Nil => {\n                close();"));
    assert!(expanded.contains("TestList::Cons(head, tail) => {\n                close();"));
    assert!(expanded.contains("let ih = induct(xs);"));
    assert!(expanded.contains("match xs {"));
    assert!(!expanded.contains(" as ih"));
    crate::surface::without_implicit_solve(|| verify_c_sources(&expanded, &[]))
        .expect("the expanded structural proof should cold-replay");
}

fn expand_top_level_tactic_for_test(
    click_source: &str,
    c_sources: &[(&str, &str)],
    function_name: &str,
    claim: ContractProofClaim,
    tactic_index: usize,
) -> Result<String, ClickError> {
    let file = parse_source_with_c_layouts(click_source, c_sources)?;
    let tokens = proof_source_tokens(click_source, &file.source_spans().implicit_proofs)?;
    let function_block = file
        .function_blocks()
        .iter()
        .find(|function| function.signature().name() == function_name)
        .ok_or_else(|| ClickError::new(format!("unknown function `{function_name}`")))?;
    let function = DeclarationSources::new(&tokens).function(function_block)?;
    if claim == ContractProofClaim::Grouped && function.grouped.is_none() {
        // The omitted proof is the implicit tail alone. It sits at the
        // contract's closing brace when it covers several claims, and at
        // the claim itself when there is one.
        assert_eq!(
            tactic_index, 0,
            "an omitted proof has only its implicit tail"
        );
        let at = if function_block.covering_proof().is_some() {
            tokens[function.body_close].span.start
        } else {
            let (clause, _) = function.clauses[0].as_ref().expect("the one claim clause");
            tokens[*clause].span.start
        };
        let position = position_at_offset(click_source, at);
        return expand_c_tactic_source_at(click_source, c_sources, position.line, position.column);
    }
    let proof = match claim {
        ContractProofClaim::Grouped => find_grouped_proof_span(&tokens, &function)?,
        ContractProofClaim::Ensure(_) | ContractProofClaim::ExceptionalEnsure(_) => {
            find_claim_proof_span(&tokens, &function, function_block, claim)?
        }
    };
    let span = find_tactic_span(&ProofTokens::new(&file, &tokens), &proof, tactic_index)?;
    let position = position_at_offset(click_source, span.start);
    expand_c_tactic_source_at(click_source, c_sources, position.line, position.column)
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_04")]
fn expands_one_grouped_tactic_without_running_the_suffix() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let click_source = r#"
verifying "identity.c";

int32 identity(int32 x) {
    ensures result == x;
} by {
    step_until(function.exit);
    close();
}
"#;

    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        ContractProofClaim::Grouped,
        0,
    )
    .expect("the first grouped tactic should expand");

    assert!(!expanded.contains("step_until(function.exit);"));
    assert!(expanded.contains("    step();\n    close();"));
    verify_c_sources(&expanded, &[("identity.c", c_source)])
        .expect("the source with one expanded tactic should re-verify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_05")]
fn expands_grouped_immutable_read_with_multiple_claim_successors() {
    let c_source = "int32 read_first(int32 p[1]) { return p[0]; }";
    let click_source = r#"
verifying "read.c";

int32 read_first(int32 p[1]) {
    views p[0..1];
    ensures result == p[0];
}
"#;

    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &[("read.c", c_source)],
        "read_first",
        ContractProofClaim::Grouped,
        0,
    )
    .expect("the grouped immutable read should have one common expansion");

    assert!(!expanded.contains("step_until(function.exit);"));
    assert!(expanded.contains("step();"), "{expanded}");
    verify_c_sources(&expanded, &[("read.c", c_source)])
        .expect("the expanded immutable read should re-verify every grouped claim");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_05")]
fn expands_nested_branch_tactic_by_source_location() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let click_source = r#"
verifying "identity.c";

int32 identity(int32 x) {
    ensures result == x;
} by {
    if x == x {
        step_until(function.exit);
        close();
    } else {
        step_until(function.exit);
        close();
    }
}
"#;
    let then_offset = click_source
        .find("        step_until(function.exit);")
        .expect("then tactic should exist")
        + 8;
    let position = position_at_offset(click_source, then_offset);
    let (expanded, capture_flat_units) = super::super::proof::count_flat_proof_units(|| {
        {
            expand_c_tactic_source_at(
                click_source,
                &[("identity.c", c_source)],
                position.line,
                position.column,
            )
        }
    });
    let expanded = expanded.expect("the nested then tactic should expand");
    assert_eq!(capture_flat_units, 1, "capture should retain one Proof");

    assert_eq!(expanded.matches("step_until(function.exit);").count(), 1);
    assert!(
        expanded.contains("    if x == x {\n        step();"),
        "{expanded}"
    );
    let (reverified, reverify_flat_units) = super::super::proof::count_flat_proof_units(|| {
        verify_c_sources(&expanded, &[("identity.c", c_source)])
    });
    reverified.expect("the source with one nested expansion should re-verify");
    assert_eq!(
        reverify_flat_units, 1,
        "the rewritten nested tactic should retain one Proof"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_05")]
fn source_positions_include_tactics_nested_in_open_blocks() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let click_source = r#"
resource known(x: int32) {
    fact x == x;
}

verifying "identity.c";

int32 identity(int32 x) {
    owns known(x);
    ensures result == x;
} by {
    with(known(x)) {
        step_until(function.exit);
    }
    close();
}
"#;
    let sources = [("identity.c", c_source)];

    let nested = c_tactic_source_position(click_source, &sources, "identity.contract", 1)
        .expect("the tactic inside `with` should have a source position");
    assert_eq!(
        nested,
        SourcePosition {
            line: 13,
            column: 9,
            origin: None
        }
    );

    let continuation = c_tactic_source_position(click_source, &sources, "identity.contract", 2)
        .expect("the tactic after `with` should retain its source position");
    assert_eq!(
        continuation,
        SourcePosition {
            line: 15,
            column: 5,
            origin: None
        }
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_05")]
fn expands_common_step_after_frontier_branch() {
    let c_source = r#"
int32 increment_selected(int32 x) {
    int32 y;
    if (x >= 0) {
        y = x;
    } else {
        y = 0;
    }
    y = y + 1;
    return y;
}
"#;
    let click_source = r#"
verifying "increment.c";

int32 increment_selected(int32 x) {
    requires x < 2147483647;
    ensures result > 0 by {
        step();
        branch ensuring {
            fact y >= 0;
            fact y < 2147483647;
        } {
            true => {
                step();
            }
            false => {
                step();
            }
        }
        step();
        step();
        close();
    }
}
"#;
    let selected_offset = click_source
        .find("        step();\n        step();\n        close();")
        .expect("common step should exist")
        + 8;
    let position = position_at_offset(click_source, selected_offset);
    let expanded = expand_c_tactic_source_at(
        click_source,
        &[("increment.c", c_source)],
        position.line,
        position.column,
    )
    .expect("common step should expand");

    verify_c_sources(&expanded, &[("increment.c", c_source)]).unwrap_or_else(|error| {
        panic!("expanded common step should check:\n{error:?}\n{expanded}")
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_06")]
fn expands_deferred_solve_after_frontier_branch() {
    let c_source = r#"
int32 positive_after_branch(int32 x) {
    int32 y;
    if (x >= 0) {
        y = x;
    } else {
        y = 0;
    }
    y = y + 1;
    return y;
}
"#;
    let click_source = r#"
verifying "positive.c";

int32 positive_after_branch(int32 x) {
    requires x < 2147483647;
    ensures result > 0 by {
        step();
        branch ensuring {
            fact y >= 0;
            fact y < 2147483647;
        } {
            true => {
                step();
            }
            false => {
                step();
            }
        }
        step();
        step();
        close();
    }
}
"#;
    let selected_offset = click_source
        .find("        close();")
        .expect("solve should exist")
        + 8;
    let position = position_at_offset(click_source, selected_offset);
    let expanded = expand_c_tactic_source_at(
        click_source,
        &[("positive.c", c_source)],
        position.line,
        position.column,
    )
    .expect("deferred solve should expand");

    verify_c_sources(&expanded, &[("positive.c", c_source)]).unwrap_or_else(|error| {
        panic!("expanded deferred solve should check:\n{error:?}\n{expanded}")
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_06")]
fn shares_equal_deferred_expansions_after_frontier_branch() {
    let c_source = r#"
int32 same_after_branch(int32 x, int32 flag) {
    int32 y;
    if (flag != 0) {
        y = x;
    } else {
        y = x;
    }
    return y;
}
"#;
    let click_source = r#"
verifying "same.c";

int32 same_after_branch(int32 x, int32 flag) {
    ensures result == x by {
        step();
        branch { true => { step(); } false => { step(); } }
        step();
        close();
    }
}
"#;
    let selected_offset = click_source
        .find("        close();")
        .expect("solve should exist")
        + 8;
    let position = position_at_offset(click_source, selected_offset);
    let expanded = expand_c_tactic_source_at(
        click_source,
        &[("same.c", c_source)],
        position.line,
        position.column,
    )
    .expect("equal deferred certificates should expand");

    assert!(!expanded.contains("if at(region(1).entry"), "{expanded}");
    verify_c_sources(&expanded, &[("same.c", c_source)]).unwrap_or_else(|error| {
        panic!("shared deferred expansion should check:\n{error:?}\n{expanded}")
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_06")]
fn expands_common_deferred_tactic_with_a_returning_branch_arm() {
    let c_source = r#"
int32 clamp_nonnegative(int32 x) {
    if (x < 0) {
        return 0;
    }
    return x;
}
"#;
    let click_source = r#"
verifying "returning.c";

int32 clamp_nonnegative(int32 x) {
    ensures result >= 0 by {
        branch {
            true => {
                step();
                close();
            }
            false => {}
        }
        step();
        close();
    }
}
"#;
    let selected_offset = click_source
        .rfind("        close();")
        .expect("common solve should exist")
        + 8;
    let position = position_at_offset(click_source, selected_offset);
    let expanded = expand_c_tactic_source_at(
        click_source,
        &[("returning.c", c_source)],
        position.line,
        position.column,
    )
    .expect("reachable continuation solve should expand");

    verify_c_sources(&expanded, &[("returning.c", c_source)]).unwrap_or_else(|error| {
        panic!("returning-arm deferred expansion should check:\n{error:?}\n{expanded}")
    });
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_06")]
fn expands_deferred_solve_after_nested_frontier_branches() {
    let c_source = r#"
int32 nested_nonnegative(int32 x, int32 flag) {
    int32 y;
    if (flag != 0) {
        if (x >= 0) {
            y = x;
        } else {
            y = 0;
        }
    } else {
        y = 0;
    }
    return y;
}
"#;
    let click_source = r#"
verifying "nested.c";

int32 nested_nonnegative(int32 x, int32 flag) {
    ensures result >= 0 by {
        step();
        branch ensuring {
            fact y >= 0;
        } {
            true => {
                branch ensuring {
                    fact y >= 0;
                } {
                    true => { step(); }
                    false => { step(); }
                }
            }
            false => { step(); }
        }
        step();
        close();
    }
}
"#;
    let (verified, flat_units) = super::super::proof::count_flat_proof_units(|| {
        verify_c_sources(click_source, &[("nested.c", c_source)])
    });
    let verified = verified.expect("nested end-of-arm interfaces should verify through Proof");
    assert_eq!(flat_units, 1, "the nested script should retain one Proof");
    let retained = verified[0]
        .expanded_proof_tactics()
        .expect("the nested proof should retain surface evidence");
    fn count_branches(tactics: &[ProofTactic]) -> usize {
        tactics
            .iter()
            .map(|tactic| match tactic {
                ProofTactic::Branch(branch) => {
                    1 + count_branches(&branch.then_tactics) + count_branches(&branch.else_tactics)
                }
                ProofTactic::If(proof_if) => {
                    count_branches(&proof_if.then_tactics) + count_branches(&proof_if.else_tactics)
                }
                ProofTactic::Open(open) => count_branches(&open.tactics),
                _ => 0,
            })
            .sum()
    }
    assert_eq!(count_branches(&retained), 2, "{retained:#?}");

    let selected_offset = click_source
        .find("        close();")
        .expect("common solve should exist")
        + 8;
    let position = position_at_offset(click_source, selected_offset);
    let expanded = expand_c_tactic_source_at(
        click_source,
        &[("nested.c", c_source)],
        position.line,
        position.column,
    );
    let expanded = expanded.expect("nested deferred solve should expand");

    verify_c_sources(&expanded, &[("nested.c", c_source)]).unwrap_or_else(|error| {
        panic!("nested deferred expansion should check:\n{error:?}\n{expanded}")
    });

    let inner_offset = click_source
        .find("            branch ensuring {")
        .expect("inner branch should exist")
        + 12;
    let inner_position = position_at_offset(click_source, inner_offset);
    let inner = expand_c_tactic_source_at(
        click_source,
        &[("nested.c", c_source)],
        inner_position.line,
        inner_position.column,
    );
    let inner = inner.expect("the retained inner branch should expand");
    verify_c_sources(&inner, &[("nested.c", c_source)]).unwrap_or_else(|error| {
        panic!("inner branch expansion should reverify:\n{error:?}\n{inner}")
    });
}

#[test]
fn locates_a_block_tactic_as_one_source_statement() {
    let source =
        "theorem t(x: int32) {\n    ensures x == x by { have x == x by close(); close(); }\n}\n";
    let file = parser::parse_file_items(source).expect("source should parse");
    let tokens = proof_source_tokens(source, &file.source_spans().implicit_proofs)
        .expect("source should scan");
    let tokens = ProofTokens::new(&file, &tokens);
    let by = tokens.iter().position(|token| token.text == "by").unwrap();
    let proof = tokens
        .blocks
        .clauses
        .at(by)
        .expect("proof should have a span")
        .span(&tokens);

    let first = find_tactic_span(&tokens, &proof, 0).expect("first tactic should exist");
    let second = find_tactic_span(&tokens, &proof, 1).expect("second tactic should exist");

    assert_eq!(&source[first], "have x == x by close();");
    assert_eq!(&source[second], "close();");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_07")]
fn hides_statement_local_opaque_call_facts_from_surface_premises() {
    let zero_c = "int32 zero() { return 0; }";
    let caller_c = "int32 caller() { int32 value; value = zero(); return value; }";
    let click_source = r#"
verifying "zero.c";
verifying "caller.c";

int32 zero() {
    ensures result == 0;
} by {
    step_until(function.exit);
    close();
}

int32 caller() {
    ensures result == 0;
} by {
    step_until(function.exit);
    close();
}
"#;
    let sources = [("zero.c", zero_c), ("caller.c", caller_c)];

    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &sources,
        "caller",
        ContractProofClaim::Grouped,
        0,
    )
    .expect("opaque call internals should not become surface premises");

    assert_eq!(expanded.matches("step_until(function.exit);").count(), 1);
    verify_c_sources(&expanded, &sources)
        .expect("the caller with one expanded tactic should re-verify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_07")]
fn opaque_call_expansion_keeps_only_consumed_ambient_conditions() {
    let positive_c = "int32 positive(int32 x) { return x; }";
    let caller_c = "int32 caller(int32 x) { int32 result; result = positive(x); return result; }";
    let click_source = r#"
verifying "positive.c";
verifying "caller.c";

int32 positive(int32 x) {
    requires 0 < x;
    ensures result == x;
}

int32 caller(int32 x) {
    requires 0 < x;
    requires x < 100;
    requires x != 37;
    ensures result == x;
}
"#;
    let sources = [("positive.c", positive_c), ("caller.c", caller_c)];

    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &sources,
        "caller",
        ContractProofClaim::Grouped,
        0,
    )
    .expect("the call should expand with its consumed precondition");
    // The call retains an explicit proof of its known precondition.
    assert_eq!(expanded.matches("step();").count(), 3, "{expanded}");
    assert_eq!(expanded.matches("step() by {").count(), 1, "{expanded}");
    verify_c_sources(&expanded, &sources).expect("the call steps should check");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_07")]
fn opaque_call_expansion_keeps_memory_condition_safety() {
    let positive_at_c =
        "struct box { int32 value; }; int32 positive_at(struct box* p) { return p->value; }";
    let caller_c = r#"struct box { int32 value; };
int32 caller(struct box* p, int32 x) {
    int32 result;
    result = positive_at(p);
    return result;
}"#;
    let click_source = r#"
verifying "positive_at.c";
verifying "caller.c";

int32 positive_at(struct box* p) {
    views p->value;
    requires 0 < p->value;
    ensures result == p->value;
}

int32 caller(struct box* p, int32 x) {
    views p->value;
    requires 0 < p->value;
    requires x < 100;
    ensures result == p->value;
}
"#;
    let sources = [("positive_at.c", positive_at_c), ("caller.c", caller_c)];

    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &sources,
        "caller",
        ContractProofClaim::Grouped,
        0,
    )
    .expect("the memory-reading precondition should expand");
    // The memory-reading prerequisite retains its explicit proof.
    assert_eq!(expanded.matches("step();").count(), 3, "{expanded}");
    assert_eq!(expanded.matches("step() by {").count(), 1, "{expanded}");
    verify_c_sources(&expanded, &sources)
        .expect("the condition and its ambient view should verify normally");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_07")]
fn expands_public_opaque_call_results_through_later_call_arguments() {
    let zero_c = "int32 zero() { return 0; }";
    let passthrough_c = "int32 passthrough(int32 x) { return x; }";
    let caller_c = r#"int32 caller() {
    int32 first;
    int32 second;
    first = zero();
    second = passthrough(first);
    return second;
}"#;
    let click_source = r#"
verifying "zero.c";
verifying "passthrough.c";
verifying "caller.c";

int32 zero() {
    ensures result == 0;
} by {
    step_until(function.exit);
    close();
}

int32 passthrough(int32 x) {
    ensures result == x;
} by {
    step_until(function.exit);
    close();
}

int32 caller() {
    ensures result == 0;
} by {
    step_until(function.exit);
    close();
}
"#;
    let sources = [
        ("zero.c", zero_c),
        ("passthrough.c", passthrough_c),
        ("caller.c", caller_c),
    ];
    let final_solve = click_source
        .rfind("close();")
        .expect("caller final solve should exist");
    let position = position_at_offset(click_source, final_solve);

    let expanded =
        expand_c_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("public call facts should compose through their receiving locals");

    assert!(expanded.contains("close();"), "{expanded}");
    assert!(!expanded.contains("call-havoc"), "{expanded}");
    assert!(!expanded.contains("symbolic-pointer"), "{expanded}");
    verify_c_sources(&expanded, &sources)
        .expect("the expanded public fact chain should independently re-verify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_08")]
fn grouped_solve_distinguishes_program_local_result_from_contract_result() {
    let zero_c = "int32 zero() { return 0; }";
    let caller_c = "int32 caller() { int32 result; result = zero(); return result; }";
    let click_source = r#"
verifying "zero.c";
verifying "caller.c";

int32 zero() {
    ensures result == 0;
} by {
    step_until(function.exit);
    close();
}

int32 caller() {
    ensures result == 0;
} by {
    step_until(function.exit);
    close();
}
"#;
    let sources = [("zero.c", zero_c), ("caller.c", caller_c)];
    let final_solve = click_source
        .rfind("close();")
        .expect("caller final solve should exist");
    let position = position_at_offset(click_source, final_solve);

    let expanded =
        expand_c_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("the grouped solve should expand across the local result assignment");

    verify_c_sources(&expanded, &sources)
        .expect("the explicit C result binding should check without aliasing contract result");

    let explicit_source = r#"
verifying "zero.c";
verifying "caller.c";

int32 zero() {
    ensures result == 0;
} by {
    step_until(function.exit);
    close();
}

int32 caller() {
    ensures result == 0;
} by {
    step_until(function.exit);
    have at(statement(2).entry, program::result) == 0 by {
        close();
    }
    have result == at(statement(2).entry, program::result) by {
        normalize();
    }
    close();
}
"#;
    verify_c_sources(explicit_source, &sources)
        .expect("`program::result` should denote the C local rather than contract result");
}

#[test]
fn selected_tactic_uses_an_unselected_callee_contract_without_proving_its_body() {
    let zero_c = "int32 zero() { return 1; }";
    let caller_c = "int32 caller() { int32 value; value = zero(); return value; }";
    let click_source = r#"
verifying "zero.c";
verifying "caller.c";

int32 zero() {
    ensures result == 0;
}

int32 caller() {
    ensures result == 0;
} by {
    step();
    step_until(function.exit);
    close();
}
"#;
    let sources = [("zero.c", zero_c), ("caller.c", caller_c)];

    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &sources,
        "caller",
        ContractProofClaim::Grouped,
        0,
    )
    .expect("capture should use the well-formed unselected callee contract");
    assert!(expanded.contains("step();"));
    let error = verify_c_sources(&expanded, &sources)
        .expect_err("whole-file verification must still reject the callee implementation proof");
    assert!(error.message().contains("zero.ensures_0"));
    assert!(error.message().contains("unclosed goal:"));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_08")]
fn grouped_solve_expansion_closes_only_the_first_open_claim() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let click_source = r#"
verifying "identity.c";

int32 identity(int32 x) {
    ensures x == 0 implies x == 0;
    ensures result == old(x);
} by {
    step_until(function.exit);
    close();
    close();
}
"#;
    let sources = [("identity.c", c_source)];

    // `solve` acts on the first open goal, so each `solve` expands to the
    // closure of one claim and the second still has its own goal.
    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &sources,
        "identity",
        ContractProofClaim::Grouped,
        1,
    )
    .expect("grouped solve should expand");

    assert!(expanded.contains("intro();"), "{expanded}");
    assert!(expanded.ends_with("\n    close();\n}\n"), "{expanded}");
    verify_c_sources(&expanded, &sources)
        .expect("the second solve should still have its goal after expansion");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_08")]
fn return_fold_retains_post_return_proof_through_expansion() {
    let sources = [("fold.c", "int f(int *p) { return 0; }")];
    let source = r#"
verifying "fold.c";
function reflexive(p: int32*) -> int32 { if p == p { 1 } else { 0 } }
resource Cell(p: int32*) {
    field tag: int32;
    owns p[0..1];
    fact reflexive(p) == 1;
}
int32 f(int32* p) {
    consumes p[0..1];
    produces out: Cell(p);
    ensures result == 0;
} by {
    step_until(function.exit);
    have reflexive(p) == 1 by { unfold(reflexive(p)); normalize(); }
    let out = fold(Cell(p), { tag: 1 });
    close();
}
"#;
    verify_c_sources(source, &sources).unwrap();
    let expanded =
        expand_top_level_tactic_for_test(source, &sources, "f", ContractProofClaim::Grouped, 3)
            .expect("the returned fold's final closer expands");
    verify_c_sources(&expanded, &sources).expect("the checked have survives explicit closers");
    let false_body = source.replace("if p == p { 1 }", "if p == p { 0 }");
    assert!(verify_c_sources(&false_body, &sources).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_08")]
fn grouped_solve_expansion_preserves_resource_scalar_and_quantified_transitions() {
    let c_source = "int32 inspect(int32 p[1], int32 x) { return 0; }";
    let click_source = r#"
verifying "inspect.c";

int32 inspect(int32 p[1], int32 x) {
    requires forall (k: int32) {
        0 <= k and k < 1 implies x == x
    };
    owns p[0..1];
    ensures result == 0;
    ensures forall (k: int32) {
        0 <= k and k < 1 implies x == x
    };
} by {
    step_until(function.exit);
    close();
}
"#;
    let sources = [("inspect.c", c_source)];

    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &sources,
        "inspect",
        ContractProofClaim::Grouped,
        1,
    )
    .expect("grouped solve should capture every newly closed claim");

    assert!(!expanded.contains("solve();"), "{expanded}");
    verify_c_sources(&expanded, &sources)
        .expect("the grouped transition certificate should re-verify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_09")]
fn grouped_solve_expansion_uses_explicit_frame_consequences() {
    let c_source = r#"
int32 increment_and_return_old(int32 p[1]) {
    int32 result;
    result = p[0];
    p[0] = 0;
    return result;
}
"#;
    let click_source = r#"
verifying "increment.c";

int32 increment_and_return_old(int32 p[1]) {
    owns p[0..1];
    ensures result == old(p[0]);
    ensures p[0] == 0;
} by {
    step_until(function.exit);
    close();
}
"#;
    let sources = [("increment.c", c_source)];

    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &sources,
        "increment_and_return_old",
        ContractProofClaim::Grouped,
        1,
    )
    .expect("grouped solve should capture frame-dependent claims");

    assert!(!expanded.contains("solve();"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c_sources(&expanded, &sources)
        .expect("the grouped frame transition certificate should re-verify");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn expansion_preserves_unfolded_resource_and_predicate_fact_forms() {
    let c_source = r#"
struct box {
    int32 len;
    int32 cap;
    int32* data;
};

int32 inspect(struct box* owner) {
    int32 ignored;
    return 0;
}
"#;
    let click_source = r#"
predicate terminated_at(data: int32[], length: int32) {
    data[length] == 0
}

resource owned_box(owner: struct box*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len < owner->cap;
    fact terminated_at(owner->data, owner->len);
    fact separate(
        memory(*owner),
        memory(owner->data[0..owner->cap])
    );
}

verifying "inspect.c";

int32 inspect(struct box* owner) {
    consumes owned_box(owner);
    ensures result == 0;
} by {
    unfold(owned_box(owner));
    unfold(terminated_at(owner->data, owner->len));
    step();
    step_until(function.exit);
    close();
}
"#;

    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &[("inspect.c", c_source)],
        "inspect",
        ContractProofClaim::Grouped,
        2,
    )
    .expect("the declaration should expand with unfolded surface facts");

    // A bare `step()` runs in the whole context: the unfolded resource and
    // predicate facts are visible to it without being spelled as premises,
    // and the expansion keeps the step as written.
    assert!(expanded.contains("step();"), "{expanded}");
    verify_c_sources(&expanded, &[("inspect.c", c_source)])
        .expect("the expansion with unfolded facts in context should verify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_09")]
fn source_position_maps_implicit_default_proofs() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let implicit = r#"verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x;
}
"#;
    assert_eq!(
        c_tactic_source_position(
            implicit,
            &[("identity.c", c_source)],
            "identity.ensures_0",
            0,
        )
        .unwrap(),
        SourcePosition {
            line: 3,
            column: 5,
            origin: None
        }
    );
    assert!(
        c_tactic_source_position(
            implicit,
            &[("identity.c", c_source)],
            "identity.ensures_0",
            2,
        )
        .is_err()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_09")]
fn expanded_uint8_facts_print_as_parseable_typed_literals() {
    let c_source = "int32 contains(uint8 p[], int32 n) { return 0; }";
    let click_source = r#"import click::bytes;
verifying "contains.c";
int32 contains(uint8 p[], int32 n) {
    requires viewable(p[0..n]);
    requires bytes::contains(p, 0, n as uint64, 'x');
    ensures bytes::contains(p, 0, n as uint64, 'x') by {
        step_until(function.exit);
        unfold(bytes::contains(p, 0, n as uint64, 'x'));
        let found = obtain(exists (found: uint64) {
            0u64 <= found and found < n as uint64 and p[found] == 'x'
        });
        witness(found);
        close();
    }
}"#;
    let offset = click_source
        .rfind("close")
        .expect("solve should be present");
    let position = position_at_offset(click_source, offset);
    let expanded = expand_c_tactic_source_at(
        click_source,
        &[("contains.c", c_source)],
        position.line,
        position.column,
    )
    .expect("uint8 proposition should expand");

    // The `solve` closes the proof the `witness` opened, so it expands to
    // that one step rather than restating the claim.
    assert!(
        expanded.contains("witness(found);\n        close();"),
        "{expanded}"
    );
    verify_c_sources(&expanded, &[("contains.c", c_source)])
        .expect("the expansion should re-verify");
    // A uint8 fact still prints as a parseable typed literal.
    let file = parse_source_with_c_layouts(click_source, &[("contains.c", c_source)])
        .expect("the sidecar parses");
    let Ensure::Proposition(claim) = file.function_blocks()[0].ensures()[0].ensure() else {
        panic!("the claim is a proposition");
    };
    assert_eq!(
        crate::surface::printing::source_click_proposition(claim),
        "click::bytes::contains(p, 0, (n as uint64), 120u8)"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_09")]
fn expanded_bitvector_facts_print_parseable_negative_literals() {
    let c_source = "int32 all_bits() { return ~0; }";
    // `~0` is -1, and a sidecar literal takes the same type it takes in C, so
    // the claim is spelled with the negative literal the expansion prints.
    let click_source = r#"verifying "all_bits.c";
int32 all_bits() {
    ensures result == -1;
}"#;
    let offset = click_source
        .find("ensures")
        .expect("the claim should be present");
    let position = position_at_offset(click_source, offset);
    let expanded = expand_c_tactic_source_at(
        click_source,
        &[("all_bits.c", c_source)],
        position.line,
        position.column,
    )
    .expect("bitvector proposition should expand");

    assert!(expanded.contains("result == -1"));
    verify_c_sources(&expanded, &[("all_bits.c", c_source)])
        .expect("printed negative literal should parse and re-verify");
}

#[test]
fn expanded_branch_certificate_uses_the_branch_entry_state() {
    let c_source = r#"int32 compare_swap2(int32 p[2]) {
    int32 tmp;
    if (p[1] < p[0]) {
        tmp = p[0];
        p[0] = p[1];
        p[1] = tmp;
    } else {
        tmp = 0;
    }
    return 0;
}"#;
    let click_source = r#"verifying "compare_swap2.c";
predicate sorted_pair(p: int32[2]) {
    p[0] <= p[1]
}
int32 compare_swap2(int32 p[2]) {
    consumes p[0..2];
    ensures sorted_pair(p);
}"#;
    let expanded_tail = expand_top_level_tactic_for_test(
        click_source,
        &[("compare_swap2.c", c_source)],
        "compare_swap2",
        ContractProofClaim::Grouped,
        0,
    );
    let expanded_tail = expanded_tail
        .expect("the implicit tail should expand its branch from retained Proof steps");
    verify_c_sources(&expanded_tail, &[("compare_swap2.c", c_source)])
        .expect("the expanded implicit tail should verify normally");
    let original_condition = "if at(region(1).entry, p[1]) < at(region(1).entry, p[0]) {";
    let corrupted_condition = "if at(region(1).entry, p[1]) >= at(region(1).entry, p[0]) {";
    let corrupted_tail = expanded_tail.replacen(original_condition, corrupted_condition, 1);
    assert_ne!(
        corrupted_tail, expanded_tail,
        "the retained branch condition should be present"
    );
    verify_c_sources(&corrupted_tail, &[("compare_swap2.c", c_source)])
        .expect_err("ordinary verification should reject a corrupted branch condition");
}

/// A branch over a field read through a struct pointer expands to a
/// condition that names the field, as a sidecar writes it.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_10")]
fn expanded_branch_condition_names_a_struct_pointer_field() {
    let c_source = "struct cell { int first; int second; };\nint pick(struct cell *p) { if (p->second > 0) { return 1; } return 0; }";
    let click_source = "verifying \"pick.c\";\nint32 pick(struct cell* p) { views p->second; ensures result >= 0; }\n";
    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &[("pick.c", c_source)],
        "pick",
        ContractProofClaim::Grouped,
        0,
    )
    .expect("a branch over a field should expand");
    assert!(
        expanded.contains("if at(region(0).entry, p->second) > at(region(0).entry, 0) {"),
        "{expanded}"
    );
    verify_c_sources(&expanded, &[("pick.c", c_source)])
        .expect("the expansion naming the field should verify");
}

/// The same through a local struct pointer.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_10")]
fn expanded_branch_condition_names_a_local_struct_pointer_field() {
    let c_source = "struct cell { int first; int second; };\nint pick(struct cell *p) { struct cell *q = p; if (q->second > 0) { return 1; } return 0; }";
    let click_source = "verifying \"pick.c\";\nint32 pick(struct cell* p) { views p->second; ensures result >= 0; }\n";
    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &[("pick.c", c_source)],
        "pick",
        ContractProofClaim::Grouped,
        0,
    )
    .expect("a branch over a field should expand");
    assert!(!expanded.contains("load<int32>("), "{expanded}");
    assert!(expanded.contains("->second) > "), "{expanded}");
    verify_c_sources(&expanded, &[("pick.c", c_source)])
        .expect("the expansion naming the field should verify");
}

/// A field of a struct nested in another, and a pointer field to a struct,
/// are written as places too.
#[test]
fn expanded_branch_condition_names_nested_and_pointer_fields() {
    let c_source = "struct inner { int x; int y; };\nstruct outer { int tag; struct inner in; struct outer *next; };\nint pick(struct outer *p) { if (p->in.y > 0) { return 1; } if (p->next == 0) { return 2; } return 0; }";
    let click_source = "verifying \"pick.c\";\nint32 pick(struct outer* p) { views p->in.y; views p->next; ensures result >= 0; }\n";
    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &[("pick.c", c_source)],
        "pick",
        ContractProofClaim::Grouped,
        0,
    )
    .expect("branches over nested fields should expand");
    assert!(expanded.contains("p->in.y) > "), "{expanded}");
    assert!(expanded.contains("p->next"), "{expanded}");
    assert!(!expanded.contains("load_"), "{expanded}");
    verify_c_sources(&expanded, &[("pick.c", c_source)])
        .expect("the expansion naming the fields should verify");
}

/// A field read through a pointer that was itself loaded from a field is
/// written as the place, `p->next->second`, not as a byte offset from it.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_10")]
fn expanded_branch_condition_names_a_field_through_a_loaded_pointer() {
    let c_source = "struct node { int first; int second; struct node *next; };\nint pick(struct node *p) { if (p->next->second > 0) { return 1; } return 0; }";
    let click_source = "verifying \"pick.c\";\nint32 pick(struct node* p) { views p->next; views p->next->second; ensures result >= 0; }\n";
    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &[("pick.c", c_source)],
        "pick",
        ContractProofClaim::Grouped,
        0,
    )
    .expect("a branch over a field through a loaded pointer should expand");
    assert!(expanded.contains("p->next->second) > "), "{expanded}");
    assert!(!expanded.contains("load_"), "{expanded}");
    verify_c_sources(&expanded, &[("pick.c", c_source)])
        .expect("the expansion naming the field should verify");
}

/// `close() using` on a `uint64` goal expands to the bridge steps it took,
/// and the expansion verifies with no `close()` left to plan. A
/// comparison and its observed reading are one fact, so an order premise is
/// carried by `close()`; type ranges and each sum's in-range identity use
/// `close()` after the two exact-result Integer
/// bounds, with no standard-library bridge theorem.
#[test]
fn uint64_arithmetic_expands_to_its_integer_bridge_steps() {
    let source = "theorem step_two(i: uint64, length: uint64) {\n    requires i <= length;\n    requires to_integer(i + 1u64) < to_integer(length);\n    requires length <= 2147483647u64;\n    ensures to_integer(i + 2u64) <= to_integer(length) by {\n        close() using { i <= length; to_integer(i + 1u64) < to_integer(length); length <= 2147483647u64; }\n    }\n}\n";
    let expanded = expand_c_claim_source_by_label(source, &[], "step_two.ensures_0")
        .expect("the uint64 arithmetic proof verifies and expands");
    for step in [
        "have to_integer((i + 1u64)) < to_integer(length) by {\n            close();",
        "have 0 <= to_integer(i) by {\n            close();",
        "have to_integer((i + 2u64)) ==",
    ] {
        assert!(expanded.contains(step), "{step}\n{expanded}");
    }
    assert!(!expanded.contains("close() using"), "{expanded}");
    verify_c_sources(&expanded, &[]).expect("the expansion verifies");
    // Without the bound on `i`, `i + 1` may wrap, and the step says so.
    let unbounded = source.replace("i <= length; to_integer(i + 1u64)", "to_integer(i + 1u64)");
    assert_ne!(unbounded, source);
    let error = verify_c_sources(&unbounded, &[]).expect_err("the sum may wrap");
    assert!(
        error.message().contains("stays within uint64"),
        "{}",
        error.message()
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn wide_arithmetic_reads_listed_bounds_at_their_named_state() {
    for carrier in ["uint64", "int64"] {
        let c_source = format!("{carrier} advance({carrier} n) {{ n = n - 4; return n; }}");
        let source = format!(
            r#"verifying "advance.c";
{carrier} advance({carrier} n) {{
    requires 4 <= n;
    requires n <= 16;
    ensures result <= 12 by {{
        mark before;
        step_until(function.exit);
        have to_integer(result) == to_integer(at(before, n)) - 4 by {{
            close() using {{
                at(before, 4 <= n);
                at(before, n <= 16);
            }}
        }}
        have result <= 12 by {{
            close() using {{
                to_integer(at(before, n)) <= 16;
                to_integer(result) == to_integer(at(before, n)) - 4;
            }}
        }}
        close();
    }}
}}"#
        );
        let sources = [("advance.c", c_source.as_str())];
        verify_c_sources(&source, &sources).expect("state bounds must verify");
        let expanded = expand_c_claim_source_by_label(&source, &sources, "advance.ensures_0")
            .expect("state bridges must expand");
        assert!(!expanded.contains("close() using"), "{expanded}");
        verify_c_sources(&expanded, &sources).expect("state bridges must independently verify");
        let missing_bound = source.replace("to_integer(at(before, n)) <= 16;", "");
        verify_c_sources(&missing_bound, &sources)
            .expect_err("a historical upper bound cannot be inferred from type bounds");
        let false_result = source.replace("result <= 12", "result <= 11");
        verify_c_sources(&false_result, &sources)
            .expect_err("state facts cannot prove a false bound");
    }
}

/// The same for a signed 64-bit goal: each sum is shown defined from its
/// Integer bounds, which together are its definedness fact, before it is
/// observed.
#[test]
fn int64_arithmetic_expands_to_its_integer_bridge_steps() {
    let source = "theorem step_two(i: int64, length: int64) {\n    requires 0i64 <= i;\n    requires length <= 2147483647i64;\n    requires i <= length;\n    requires to_integer(i + 1i64) < to_integer(length);\n    ensures to_integer(i + 2i64) <= to_integer(length) by {\n        close() using { 0i64 <= i; i <= length; to_integer(i + 1i64) < to_integer(length); length <= 2147483647i64; }\n    }\n}\n";
    let expanded = expand_c_claim_source_by_label(source, &[], "step_two.ensures_0")
        .expect("the int64 arithmetic proof verifies and expands");
    for step in [
        "have (to_integer(i) + 1) <= 9223372036854775807 by {",
        "have to_integer((i + 2i64)) ==",
        "to_integer((i + 1i64)) < to_integer(length)",
    ] {
        assert!(expanded.contains(step), "{step}\n{expanded}");
    }
    assert!(!expanded.contains("close() using"), "{expanded}");
    verify_c_sources(&expanded, &[]).expect("the expansion verifies");
    // Without an upper bound on `i`, `i + 1` may overflow above. (A lower
    // bound is not needed: `i`'s own `int64` range keeps `i + 1` above
    // `INT64_MIN`.)
    let unbounded = source.replace("{ 0i64 <= i; i <= length;", "{ 0i64 <= i;");
    assert_ne!(unbounded, source);
    let error = verify_c_sources(&unbounded, &[]).expect_err("the sum may overflow");
    assert!(
        error.message().contains("stays within int64"),
        "{}",
        error.message()
    );
}

/// The braces the parser recorded around function `name`'s clauses, found
/// among the source's tokens.
fn parsed_function_body(source: &str, name: &str) -> Result<FunctionSource, ClickError> {
    let file = parser::parse_file_items(source)?;
    let tokens = proof_source_tokens(source, &file.source_spans().implicit_proofs)?;
    let block = file
        .function_blocks()
        .iter()
        .find(|block| block.signature().name() == name)
        .ok_or_else(|| ClickError::new(format!("no function block `{name}`")))?;
    DeclarationSources::new(&tokens).function(block)
}

/// A Rust head's generic parameters come between its name and its
/// parameters, and a callable bound has its own parentheses and `->`.
#[test]
fn a_generic_rust_head_is_located_by_its_path() {
    let source = "verifying \"lib.rs\";\nfn lib::apply<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {\n    ensures 0 == 0;\n}\nfn lib::keep<'a>(x: &'a i32) -> i32 {\n    ensures 1 == 1;\n}\n";
    let apply = parsed_function_body(source, "__rust_q_I3_lib_I5_apply").expect("the generic head");
    let keep = parsed_function_body(source, "__rust_q_I3_lib_I4_keep").expect("the lifetime head");
    assert!(apply.body_open < apply.body_close && apply.body_close < keep.body_open);
    assert!(parsed_function_body(source, "Fn").is_err());
}

/// A sidecar writes an inherent method inside its `impl` block; the block
/// the parser builds for it records the method's own body.
#[test]
fn an_inherent_method_is_located_inside_its_impl_block() {
    let source = "verifying \"lib.rs\";\nimpl adler2::Adler32 {\n    fn compute(&mut self, seed: u32) {\n        ensures 0 == 0;\n    } by { step_until(function.exit); close(); }\n}\n";
    let tokens = plain_source_tokens(source).unwrap();
    let name = "__rust_q_I6_adler2_T29___rust_q_I6_adler2_I7_Adler32_I7_compute";
    let body = parsed_function_body(source, name).expect("the parser reads the method's body");
    assert_eq!(tokens[body.body_open - 1].text, ")");
    assert_eq!(tokens[body.body_close + 1].text, "by");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_10")]
fn expanded_contract_let_facts_remain_source_indexable() {
    let c_source = "int32 increment(int32 x) { return x + 1; }";
    let click_source = r#"verifying "increment.c";
int32 increment(int32 x) {
    let max: int32 = 2147483647;
    let expected: int32 = x + 1;
    requires x < max;
    ensures result_value: result == expected;
}"#;
    let offset = click_source
        .find("ensures")
        .expect("the claim should be present");
    let position = position_at_offset(click_source, offset);
    let expanded = expand_c_tactic_source_at(
        click_source,
        &[("increment.c", c_source)],
        position.line,
        position.column,
    )
    .expect("contract-let proof should expand");

    // The step runs in the whole context; the contract `let` needs no
    // spelling as a premise. The expansion must still verify.
    verify_c_sources(&expanded, &[("increment.c", c_source)])
        .expect("parenthesized contract lets should re-verify");
    c_tactic_source_position(
        &expanded,
        &[("increment.c", c_source)],
        "increment.result_value",
        0,
    )
    .expect("semicolons inside contract lets must not split source tactics");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_11")]
fn expanded_post_execution_apply_retains_its_facts_for_the_closer() {
    let c_source = "int32 inspect(uint8 p[], uint64 len) { return 0; }";
    let click_source = r#"import click::c::string;
verifying "inspect.c";
int32 inspect(uint8 p[], uint64 len) {
    requires viewable(p[0..len + 1u64]);
    requires string::len(p, len);
    ensures p[len] == '\0' by {
        step_until(function.exit);
        apply(string::len_has_terminator(p, len));
        close();
    }
}"#;
    let offset = click_source.find("apply").expect("apply should be present");
    let position = position_at_offset(click_source, offset);
    let expanded = expand_c_tactic_source_at(
        click_source,
        &[("inspect.c", c_source)],
        position.line,
        position.column,
    )
    .expect("post-execution apply should expand");

    assert!(expanded.contains("apply(string::len_has_terminator(p, len));"));
    verify_c_sources(&expanded, &[("inspect.c", c_source)])
        .expect("explicit apply conclusions should remain available to the trailing solve");
}

#[test]
fn expansion_retains_callees_used_by_an_earlier_claim() {
    let callee_source = r#"int32 set_cell(int32 p[], int32 value) {
    p[0] = value;
    return value;
}"#;
    let caller_source = r#"int32 set_then_read(int32 p[], int32 value) {
    int32 ignored;
    ignored = set_cell(p, value);
    return p[0];
}"#;
    let click_source = r#"verifying "set_cell.c";
verifying "set_then_read.c";
int32 set_cell(int32 p[], int32 value) {
    owns p[0..1];
    ensures p[0] == value;
    ensures result == value;
}
int32 set_then_read(int32 p[], int32 value) {
    owns p[0..1] by {
        step();
        step();
        step();
        step();
    }
    ensures result == value by {
        step();
        step();
        step();
        step();
        close();
    }
}"#;
    let sources = [
        ("set_cell.c", callee_source),
        ("set_then_read.c", caller_source),
    ];
    let position = c_tactic_source_position(click_source, &sources, "set_then_read.ensures_0", 0)
        .expect("later claim should have a source tactic");
    let expanded =
        expand_c_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("selected later-claim tactic should expand with the callee available");

    verify_c_sources(&expanded, &sources)
        .expect("expanded later claim should re-verify with its earlier claim");
}

#[test]
fn expands_a_deferred_tactic_in_one_nested_proof_branch() {
    let c_source = r#"int32 nested(int32 x) {
    int32 y;
    if (x >= 0) {
        y = x;
        if (y > 0) { y = y + 1; } else { y = 0; }
    } else {
        y = 0;
    }
    return y;
}"#;
    let click_source = r#"verifying "nested.c";
int32 nested(int32 x) {
    requires x < 2147483647;
    ensures result >= 0 by {
        step();
        if x >= 0 {
            step();
            step();
            if y > 0 {
                step();
                step();
                step();
                close();
            } else {
                step();
                step();
                step();
                close();
            }
        } else {
            step();
            step();
            step();
            close();
        }
    }
}"#;
    let needle = "step();\n                step();\n                step();\n                close";
    let offset = click_source
        .find(needle)
        .map(|start| start + needle.rfind("close").unwrap())
        .expect("inner else solve should be present");
    let position = position_at_offset(click_source, offset);
    let (verified, original_flat_units) =
        proof::count_flat_proof_units(|| verify_c_sources(click_source, &[("nested.c", c_source)]));
    verified.expect("nested source proof should stay on Proof");
    assert_eq!(
        original_flat_units, 1,
        "nested source proof split its Proof"
    );

    let (expanded, expansion_flat_units) = proof::count_flat_proof_units(|| {
        {
            {
                expand_c_tactic_source_at(
                    click_source,
                    &[("nested.c", c_source)],
                    position.line,
                    position.column,
                )
            }
        }
    });
    let expanded = expanded.expect("selected nested-branch solve should expand");
    assert_eq!(expansion_flat_units, 1, "nested expansion split its Proof");

    let end = offset + "close();".len();
    let line_start = click_source[..offset].rfind('\n').unwrap() + 1;
    assert!(expanded.starts_with(&click_source[..line_start]));
    assert!(expanded.ends_with(&click_source[end..]));
    assert_ne!(expanded, click_source);
    let (reverified, reverify_flat_units) =
        proof::count_flat_proof_units(|| verify_c_sources(&expanded, &[("nested.c", c_source)]));
    reverified.expect("sibling proof cases must not steal the deferred capture");
    assert_eq!(
        reverify_flat_units, 1,
        "rewritten nested proof split its Proof"
    );

    let leading = "if x >= 0 {\n            step();";
    let leading_offset = click_source
        .find(leading)
        .map(|start| start + leading.rfind("step").unwrap())
        .expect("outer then leading step should be present");
    let leading_position = position_at_offset(click_source, leading_offset);
    let (leading_expanded, leading_flat_units) = proof::count_flat_proof_units(|| {
        {
            {
                expand_c_tactic_source_at(
                    click_source,
                    &[("nested.c", c_source)],
                    leading_position.line,
                    leading_position.column,
                )
            }
        }
    });
    let leading_expanded = leading_expanded.expect("leading smart branch step should expand");
    assert_eq!(leading_flat_units, 1, "leading expansion split its Proof");

    assert!(
        leading_expanded.contains("step();"),
        "leading smart step did not extract its checked operation: {leading_expanded}"
    );
    let (leading_reverified, _) = proof::count_flat_proof_units(|| {
        verify_c_sources(&leading_expanded, &[("nested.c", c_source)])
    });
    leading_reverified.expect("expanded leading branch step should reverify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_11")]
fn expanded_symbolic_range_propositions_use_parser_syntax() {
    let c_source = "int32 identity(int32 x, int32 n) { return x; }";
    let click_source = r#"verifying "identity.c";
int32 identity(int32 x, int32 n) {
    requires (0..n).any(|k| { k == x });
    ensures same_any: (0..n).any(|k| { k == x });
}"#;
    let offset = click_source
        .find("ensures")
        .expect("the claim should be present");
    let position = position_at_offset(click_source, offset);
    let expanded = expand_c_tactic_source_at(
        click_source,
        &[("identity.c", c_source)],
        position.line,
        position.column,
    )
    .expect("symbolic range proposition should expand");

    assert!(expanded.contains("(0..n).any(|k| { k == x })"));
    verify_c_sources(&expanded, &[("identity.c", c_source)])
        .expect("printed symbolic range proposition should re-verify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_11")]
fn expands_single_smart_and_default_function_proofs_by_source_location() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let smart = r#"verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x by { step_until(function.exit); close(); }
}
"#;
    let smart_position = position_at_offset(smart, smart.find("close").unwrap());
    let smart_expanded = expand_c_tactic_source_at(
        smart,
        &[("identity.c", c_source)],
        smart_position.line,
        smart_position.column,
    )
    .expect("single smart proof should expand as a whole proof");
    assert!(smart_expanded.contains("step_until(function.exit);"));
    assert!(!smart_expanded.contains("solve();"));
    verify_c_sources(&smart_expanded, &[("identity.c", c_source)]).unwrap();

    let implicit = r#"verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x;
}
"#;
    let implicit_position = position_at_offset(implicit, implicit.find("ensures").unwrap());
    let implicit_expanded = expand_c_tactic_source_at(
        implicit,
        &[("identity.c", c_source)],
        implicit_position.line,
        implicit_position.column,
    )
    .expect("default proof should expand from its clause coordinate");
    assert!(implicit_expanded.contains("ensures result == x by {"));
    verify_c_sources(&implicit_expanded, &[("identity.c", c_source)]).unwrap();
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_11")]
fn whole_function_proof_expansion_skips_unrelated_broken_proofs() {
    let good_c = "int32 good(int32 x) { return x; }";
    let bad_c = "int32 bad(int32 x) { return x; }";
    let click_source = r#"verifying "good.c";
verifying "bad.c";
int32 good(int32 x) {
    ensures result == x;
}
int32 bad(int32 x) {
    ensures result == x + 1 by close();
}
"#;
    let sources = [("good.c", good_c), ("bad.c", bad_c)];
    verify_c_sources(click_source, &sources)
        .expect_err("the unrelated bad proof should fail complete verification");
    let selected = position_at_offset(click_source, click_source.find("ensures").unwrap());

    let expanded =
        expand_c_tactic_source_at(click_source, &sources, selected.line, selected.column)
            .expect("whole-proof expansion should verify only the selected function");

    assert!(expanded.contains("ensures result == x by {"));
    verify_c_sources_at(&expanded, &sources, selected.line, selected.column)
        .expect("the expanded selected function should verify independently");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_12")]
fn partial_tactic_expansion_skips_unrelated_broken_proofs() {
    let good_c = "int32 good(int32 x) { return x; }";
    let bad_c = "int32 bad(int32 x) { return x; }";
    let click_source = r#"verifying "good.c";
verifying "bad.c";
int32 good(int32 x) {
    ensures result == x by { step_until(function.exit); close(); }
}
int32 bad(int32 x) {
    ensures result == x + 1 by close();
}
"#;
    let sources = [("good.c", good_c), ("bad.c", bad_c)];
    verify_c_sources(click_source, &sources)
        .expect_err("the unrelated bad proof should fail complete verification");
    let selected_offset = click_source.find("step_until(function.exit);").unwrap();
    let selected = position_at_offset(click_source, selected_offset);

    let expanded =
        expand_c_tactic_source_at(click_source, &sources, selected.line, selected.column)
            .expect("partial expansion should verify only the selected function");

    assert_ne!(expanded, click_source);
    assert_eq!(
        &expanded[..selected_offset],
        &click_source[..selected_offset]
    );
    let unselected_suffix = &click_source[selected_offset + "step_until(function.exit);".len()..];
    assert!(expanded.ends_with(unselected_suffix));
    let relocated = c_tactic_source_position(&expanded, &sources, "good.ensures_0", 0).unwrap();
    verify_c_sources_at(&expanded, &sources, relocated.line, relocated.column)
        .expect("the expanded selected function should verify independently");
    verify_c_sources(&expanded, &sources)
        .expect_err("whole-file verification should still see the unrelated failure");
}

#[test]
fn tactic_expansion_does_not_select_a_broken_callee_implementation() {
    let callee_c = "int32 callee(int32 x) { return x + 1; }";
    let caller_c = "int32 caller(int32 x) { int32 result; result = callee(x); return result; }";
    let click_source = r#"verifying "callee.c";
verifying "caller.c";
int32 callee(int32 x) {
    ensures result == x;
}
int32 caller(int32 x) {
    ensures result == x;
}
"#;
    let sources = [("callee.c", callee_c), ("caller.c", caller_c)];
    let selected = position_at_offset(click_source, click_source.rfind("ensures").unwrap());
    verify_c_sources_at(click_source, &sources, selected.line, selected.column)
        .expect("the selected caller should verify under the callee interface");

    let expanded =
        expand_c_tactic_source_at(click_source, &sources, selected.line, selected.column)
            .expect("the selected caller expansion should assume the callee contract");
    let relocated = c_tactic_source_position(&expanded, &sources, "caller.ensures_0", 0).unwrap();
    verify_c_sources_at(&expanded, &sources, relocated.line, relocated.column)
        .expect("the expanded caller should verify under the callee interface");
    let error = verify_c_sources(&expanded, &sources)
        .expect_err("whole-file verification must still reject the callee proof");
    assert!(error.message().contains("callee.ensures_0"));
}

#[test]
fn expands_selected_tactics_in_branched_execution_by_path() {
    let c_source = r#"int32 write_selected(int32 p[2], int32 flag) {
    if (flag) {
        p[0] = 1;
        return 0;
    } else {
        p[1] = 1;
        return 1;
    }
}"#;
    let click_source = r#"verifying "write_selected.c";
int32 write_selected(int32 p[2], int32 flag) {
    consumes p[0..2];
    ensures result == 0 or result == 1;
} by {
    if flag != 0 {
        step_until(function.exit);
        have result + 1 == 1 by close();
    } else {
        step_until(function.exit);
        have result - 1 == 0 by close();
    }
}
"#;
    let sources = [("write_selected.c", c_source)];
    let verified = verify_c_sources(click_source, &sources);
    verified.expect("branched baseline should verify");
    for (selected_text, selected_smart) in [
        ("have result + 1", "have result + 1 == 1 by close()"),
        ("have result - 1", "have result - 1 == 0 by close()"),
    ] {
        let selected_offset = click_source.find(selected_text).unwrap();
        let selected = position_at_offset(click_source, selected_offset);

        let expanded =
            expand_c_tactic_source_at(click_source, &sources, selected.line, selected.column)
                .expect("one branch's smart have should expand by its execution path");

        assert!(!expanded.contains(selected_smart));
        assert!(expanded.contains("if flag != 0"));
        verify_c_sources(&expanded, &sources)
            .expect("path-aligned branch expansion should check as a complete proof");
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_12")]
fn pure_theorem_expansion_is_certificate_backed_and_idempotent() {
    let source = r#"theorem incremented_zero_is_one(before: int32, after: int32) {
    requires before == 0;
    requires after == before + 1;
    ensures after == 1 by {
        rewrite(after, before + 1);
        rewrite(before, 0);
        close();
    }
}
"#;
    let expanded_once = expand_pure_theorem_source(source, &[], "incremented_zero_is_one", 0)
        .expect("smart theorem script should expand");
    let expanded_twice =
        expand_pure_theorem_source(&expanded_once, &[], "incremented_zero_is_one", 0)
            .expect("expanded theorem certificate should expand again");

    assert!(!expanded_once.contains("solve"));
    assert_eq!(expanded_once, expanded_twice);
    let verified =
        verify_click_theorems(&expanded_once).expect("expanded theorem should re-verify");
    verified[0]
        .proof_certificate()
        .expect("expanded theorem should retain a surface certificate");
}

#[test]
fn contract_refinement_theorem_expands_with_its_concrete_c_environment() {
    let c_source = r#"void set_one_if_active(int32 active, int32* cell) {
    if (active != 0) {
        cell[0] = 1;
    }
}"#;
    let click_source = r#"
resource optional_cell(active: int32, cell: int32*) {
    if active != 0 {
        owns cell[0..1];
    }
}

verifying "set_one.c";

contract void MakePositive(int32 active, int32* cell) {
    owns optional_cell(active, cell);
    ensures active != 0 implies cell[0] > 0;
}

void set_one_if_active(int32 active, int32* cell) {
    owns optional_cell(active, cell);
    ensures active != 0 implies cell[0] == 1;
} by {
    if active != 0 {
        unfold(optional_cell(active, cell));
        step_until(function.exit);
        fold(optional_cell(active, cell));
        close();
    } else {
        unfold(optional_cell(active, cell));
        step_until(function.exit);
        fold(optional_cell(active, cell));
        close();
    }
}

theorem set_one_is_make_positive() {
    ensures MakePositive(&set_one_if_active) by {
        unfold(MakePositive(&set_one_if_active));
        if active != 0 {
            close();
        } else {
            close();
        }
    }
}
"#;
    let sources = [("set_one.c", c_source)];

    let expanded =
        expand_pure_theorem_source(click_source, &sources, "set_one_is_make_positive", 0)
            .expect("contract-refinement theorem should expand with its concrete target");
    let theorem = &expanded[expanded
        .find("theorem set_one_is_make_positive")
        .expect("expanded source should retain the theorem")..];
    assert!(theorem.contains("intro();"), "{theorem}");
    assert!(!theorem.contains("extract("), "{theorem}");
    assert!(!theorem.contains("solve();"), "{theorem}");
    verify_c_sources(&expanded, &sources)
        .expect("expanded contract-refinement theorem should re-verify with its C target");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_12")]
fn pure_mixed_linear_smart_script_expands_the_retained_proof_object_path() {
    let source = r#"
        theorem required(x: int32) {
            requires x >= 0;
            ensures x >= 0;
        }

        theorem applied_then_solve(x: int32) {
            requires (x >= 0) and (x <= 10);
            ensures (x >= 0) and (x >= 0) by {
                have x >= 0 by close();
                apply(required(x));
                close();
            }
        }
    "#;
    let expanded = expand_pure_theorem_source(source, &[], "applied_then_solve", 0)
        .expect("the checked pure theorem path should expand");
    let selected = &expanded[expanded
        .find("theorem applied_then_solve")
        .expect("expanded source should retain the selected theorem")..];
    assert!(selected.contains("apply(required(x));"), "{selected}");
    assert!(selected.contains("have x >= 0 by {"), "{selected}");
    assert!(selected.contains("close();"), "{selected}");
    assert!(!selected.contains("solve();"), "{selected}");
    verify_click_theorems(&expanded)
        .expect("the serialized pure theorem certificate should independently reverify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_12")]
fn pure_branch_local_apply_expands_the_retained_proof_object_paths() {
    let source = r#"
        theorem equality_case(x: int32) {
            requires x == 0;
            ensures x == 0 or not (x == 0) by {
                close();
            }
        }

        theorem inequality_case(x: int32) {
            requires not (x == 0);
            ensures x == 0 or not (x == 0) by {
                close();
            }
        }

        theorem branch_apply(x: int32) {
            ensures x == 0 or not (x == 0) by {
                if x == 0 {
                    apply(equality_case(x));
                    close();
                } else {
                    apply(inequality_case(x));
                    close();
                }
            }
        }
    "#;
    let expanded = expand_pure_theorem_source(source, &[], "branch_apply", 0)
        .expect("the checked branch-local theorem paths should expand");
    let selected = &expanded[expanded
        .find("theorem branch_apply")
        .expect("expanded source should retain the selected theorem")..];
    assert!(selected.contains("apply(equality_case(x));"), "{selected}");
    assert!(
        selected.contains("apply(inequality_case(x));"),
        "{selected}"
    );
    assert!(!selected.contains("solve();"), "{selected}");
    verify_click_theorems(&expanded)
        .expect("the serialized branch-local certificates should independently reverify");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_13")]
fn pure_nested_have_branch_apply_expands_the_retained_proof_object_scope() {
    let source = r#"
        theorem equality_case_nested(x: int32) {
            requires x == 0;
            ensures x == 0 or not (x == 0) by {
                close();
            }
        }

        theorem inequality_case_nested(x: int32) {
            requires not (x == 0);
            ensures x == 0 or not (x == 0) by {
                close();
            }
        }

        theorem nested_branch_apply(x: int32) {
            ensures x == 0 or not (x == 0) by {
                have x == 0 or not (x == 0) by {
                    if x == 0 {
                        apply(equality_case_nested(x));
                        close();
                    } else {
                        apply(inequality_case_nested(x));
                        close();
                    }
                }
                close();
            }
        }
    "#;
    let expanded = expand_pure_theorem_source(source, &[], "nested_branch_apply", 0)
        .expect("the checked nested branch path should expand");
    let selected = &expanded[expanded
        .find("theorem nested_branch_apply")
        .expect("expanded source should retain the selected theorem")..];
    assert!(
        selected.contains("have x == 0 or") && selected.contains("if x == 0"),
        "{selected}"
    );
    assert!(
        selected.contains("apply(equality_case_nested(x));")
            && selected.contains("apply(inequality_case_nested(x));"),
        "{selected}"
    );
    assert!(!selected.contains("solve();"), "{selected}");
    verify_click_theorems(&expanded)
        .expect("the serialized nested pure branch should independently reverify");
}

/// An `extern` contract is assumed. Its clauses have no proof, so the
/// implicit `solve` of an unproved clause is not a site: `click audit` used to
/// list one per clause and then fail to expand it, reporting that the
/// function `has no verified ensures clause`.
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_13")]
fn smart_inventory_skips_assumed_extern_contracts() {
    let c_source = "int32 child(int32 x);\nint32 parent(int32 x) { return child(x); }\n";
    let source = r#"
verifying "calls.c";

extern int32 child(int32 x) {
    requires x >= 0;
    ensures result == x;
}

int32 parent(int32 x) {
    requires x >= 0;
    ensures result == x;
}
"#;
    let c_sources = [("calls.c", c_source)];
    verify_c_sources(source, &c_sources).expect("the caller verifies against the assumed contract");
    let sites = c_smart_tactic_source_sites(source, &c_sources).unwrap();
    assert_eq!(
        sites
            .iter()
            .map(|site| site.claim_label.as_str())
            .collect::<Vec<_>>(),
        ["parent.ensures_0"]
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_13")]
fn smart_inventory_does_not_invent_solve_sites_for_kernel_axiom_declarations() {
    let source = r#"
theorem int32_le_antisymmetric(left: int32, right: int32) {
    requires left <= right;
    requires right <= left;
    ensures left == right;
}

theorem ordinary(x: int32) {
    ensures x == x by { close(); }
}
"#;
    verify_click_theorems(source).unwrap();
    let sites = c_smart_tactic_source_sites(source, &[]).unwrap();
    assert_eq!(sites.len(), 1);
    assert_eq!(sites[0].claim_label, "ordinary.ensures_0");
    assert_eq!(sites[0].tactic_name, "close");
    assert!(
        verify_click_theorems(&source.replace("ensures left == right", "ensures left != right"))
            .is_err(),
        "kernel axiom declarations must still be checked"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_13")]
fn smart_inventory_keeps_refinement_proofs_named_like_arithmetic_axioms() {
    let source = r#"
contract int32 Identity(int32 x) { ensures result == x; }
theorem int32_le_antisymmetric() {
    ensures Identity(&identity) by { unfold(Identity(&identity)); close(); }
}
"#;
    let sites = c_smart_tactic_source_sites(source, &[]).unwrap();
    assert_eq!(sites.len(), 1);
    assert_eq!(sites[0].claim_label, "int32_le_antisymmetric.ensures_0");
    assert_eq!(sites[0].tactic_name, "close");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_14")]
fn builtin_nat_integer_laws_expand_and_reject_invalid_conversions() {
    for (parameters, requirements, goal, application) in [
        (
            "",
            "",
            "to_integer(Nat::Zero) == 0",
            "nat::to_integer_zero()",
        ),
        (
            "n: Nat",
            "",
            "to_integer(Nat::Succ(n)) == to_integer(n) + 1",
            "nat::to_integer_succ(n)",
        ),
        (
            "n: Nat",
            "",
            "to_integer(n) >= 0",
            "nat::to_integer_nonnegative(n)",
        ),
        (
            "n: Nat",
            "",
            "to_nat(to_integer(n)) == n",
            "nat::to_nat_to_integer(n)",
        ),
        (
            "z: Integer",
            "requires z >= 0;",
            "to_integer(to_nat(z)) == z",
            "nat::to_integer_to_nat(z)",
        ),
        ("", "", "to_nat(0) == Nat::Zero", "nat::to_nat_zero()"),
    ] {
        let source = format!(
            "theorem client({parameters}) {{ {requirements} ensures {goal} by {{ apply({application}); }} }}"
        );
        verify_c_sources(&source, &[])
            .unwrap_or_else(|error| panic!("{source}\n{}", error.message()));
        let expanded = expand_c_claim_source_by_label(&source, &[], "client.ensures_0").unwrap();
        verify_c_sources(&expanded, &[]).unwrap();
    }
    for source in [
        "theorem bad(z: Integer) { ensures to_integer(to_nat(z)) == z by { apply(nat::to_integer_to_nat(z)); } }",
        "theorem bad() { ensures to_nat(-1) == to_nat(-1) by normalize; }",
        "theorem bad(x: int32) { ensures to_nat(x) == to_nat(x) by normalize; }",
        "theorem bad() { ensures to_integer(Nat::Zero) == 1 by { apply(nat::to_integer_zero()); } }",
        "theorem bad() { ensures to_nat() == Nat::Zero by normalize; }",
        "theorem bad(z: Integer) { requires z >= 0; ensures to_nat(z, z) == to_nat(z) by normalize; }",
    ] {
        assert!(verify_c_sources(source, &[]).is_err(), "{source}");
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_14")]
fn nat_addition_agrees_with_integer_addition_and_rechecks_expansion() {
    let source = "theorem client(a: Nat, b: Nat) { ensures to_integer(nat::add(a, b)) == to_integer(a) + to_integer(b) by { apply(nat::to_integer_add(a, b)); } }";
    verify_c_sources(source, &[]).unwrap();
    let expanded = expand_c_claim_source_by_label(source, &[], "client.ensures_0").unwrap();
    verify_c_sources(&expanded, &[]).unwrap();
    assert!(
        verify_c_sources(
            &source.replace("+ to_integer(b)", "+ to_integer(b) + 1"),
            &[]
        )
        .is_err()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_14")]
fn signed_to_unsigned_interval_comparisons_expand_and_recheck_both_sides() {
    for goal in ["1u32 <= (x as uint32)", "(x as uint32) <= 4u32"] {
        let source = format!(
            "theorem cast_bound(x: int32) {{ requires 0 < x; requires x <= 4; ensures {goal} by {{ close() using {{ 0 < x; x <= 4; }} }} }}"
        );
        verify_c_sources(&source, &[]).unwrap();
        let expanded =
            expand_c_claim_source_by_label(&source, &[], "cast_bound.ensures_0").unwrap();
        verify_c_sources(&expanded, &[]).unwrap();
        assert!(verify_c_sources(&source.replace(goal, "5u32 <= (x as uint32)"), &[]).is_err());
    }
}

/// `source_tactic_width` numbers the tactics inside a proof `cases` and a call
/// `outcomes` block, so the site inventory, the source span list, and the
/// nested-proof test must walk those arms too. Before they did, a smart tactic
/// inside either block was missing from the inventory, and the span list fell
/// out of step with the numbering: `cases` read as two tactics, so every
/// location in or after the block failed to resolve ("source location does
/// not select a smart tactic").
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_14")]
fn smart_sites_inside_and_after_cases_and_outcomes_resolve_to_their_source() {
    let source = r#"
theorem pick_nonzero(r: int32) {
    requires r == 18 or r == -1;
    ensures r != 0 by {
        cases {
            r == 18 => {
                have r > 0 by { close(); }
            }
            r == -1 => {
                have r < 0 by { close(); }
            }
        }
        close();
    }
}
"#;
    let sites = c_smart_tactic_source_sites(source, &[]).expect("cases sites are indexed");
    let indexes = sites
        .iter()
        .map(|site| (site.source_index, site.tactic_name.as_str()))
        .collect::<Vec<_>>();
    assert_eq!(
        indexes,
        vec![(1, "close"), (2, "close"), (3, "close")],
        "{sites:?}"
    );
    let final_solve = "close();\n    }\n}";
    for (index, needle) in [
        (1, "have r > 0 by { close();"),
        (2, "have r < 0 by { close();"),
        (3, final_solve),
    ] {
        let owner = source.find(needle).unwrap();
        let close = owner + needle.find("close();").unwrap();
        let position = c_tactic_source_position(source, &[], "pick_nonzero.ensures_0", index)
            .unwrap_or_else(|error| panic!("site {index} has no source position: {error:?}"));
        assert_eq!(position, position_at_offset(source, owner), "site {index}");
        let site = sites
            .iter()
            .find(|site| site.source_index == index)
            .unwrap();
        assert_eq!(
            site.position,
            position_at_offset(source, close),
            "site {index}"
        );
    }
    let after = position_at_offset(source, source.find(final_solve).unwrap());
    let expanded = expand_c_tactic_source_at(source, &[], after.line, after.column)
        .expect("the smart tactic after `cases` expands");
    verify_c_sources(&expanded, &[]).expect("the expanded `cases` proof re-verifies");

    let c_source =
        "int32 helper(int32 x) { return x; }\nint32 client(int32 x) { return helper(x); }\n";
    let outcomes = r#"verifying "outcomes_sites.c";
int32 client(int32 x) {
    ensures result == x;
} by {
    step();
    outcomes {
        returned => {
            close();
        }
        threw => {
            close();
        }
    }
    close();
}
"#;
    let c_sources = [("outcomes_sites.c", c_source)];
    let sites =
        c_smart_tactic_source_sites(outcomes, &c_sources).expect("outcomes sites are indexed");
    let indexes = sites
        .iter()
        .map(|site| (site.source_index, site.tactic_name.as_str()))
        .collect::<Vec<_>>();
    assert_eq!(
        indexes,
        vec![(2, "close"), (3, "close"), (4, "close")],
        "{sites:?}"
    );
    for (index, needle) in [
        (2, "close();\n        }\n        threw"),
        (3, "close();\n        }\n    }"),
        (4, "close();\n}"),
    ] {
        let position = c_tactic_source_position(outcomes, &c_sources, "client.contract", index)
            .unwrap_or_else(|error| panic!("site {index} has no source position: {error:?}"));
        assert_eq!(
            position,
            position_at_offset(outcomes, outcomes.find(needle).unwrap()),
            "site {index}"
        );
    }
}

#[test]
fn load_equality_chain_across_a_call_expands_and_replays() {
    let path = std::path::Path::new("solve_composes_a_pointer_field_chain_across_a_call.md");
    let fixture = crate::cli::parse_mdtest(
        path,
        &mdtest_markdown("solve_composes_a_pointer_field_chain_across_a_call.md"),
    )
    .unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = crate::cli::source_refs(&fixture.c_sources);
    let expanded = expand_c_claim_source_by_label(source, &sources, "caller.contract")
        .unwrap_or_else(|error| panic!("{}", error.message()));
    assert!(!expanded.contains("solve();"), "{expanded}");
    crate::surface::check_audit_claim("caller.contract", true, || {
        verify_c_sources(&expanded, &sources).map_err(|error| error.report())
    })
    .unwrap();
}

#[test]
fn specification_pointer_load_equality_expands_to_known() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/egraph_resource_pointer_load_alias.md");
    let fixture = crate::cli::read_mdtest(&path).expect("pointer-load fixture");
    let source = fixture.click_source.as_deref().expect("Click source");
    let sources = crate::cli::source_refs(&fixture.c_sources);
    verify_c_sources(source, &sources).expect("original specification equality verifies");
    let equality = source
        .find("have p->next == id->next")
        .expect("load equality claim");
    let tactic = equality
        + source[equality..]
            .find("close();")
            .expect("equality tactic");
    let position = position_at_offset(source, tactic);
    let expanded = expand_c_tactic_source_at(source, &sources, position.line, position.column)
        .expect("logical load equality should expand");
    assert!(expanded.contains("close();"), "{expanded}");
    assert!(!expanded.contains("normalize("), "{expanded}");
    assert!(
        !expanded.contains("MemoryLoad") && !expanded.contains("__click_"),
        "{expanded}"
    );
    verify_c_sources(&expanded, &sources)
        .expect("expanded known certificate independently verifies");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn recursive_child_alias_fold_expands_and_rechecks_without_load_claims() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/egraph_recursive_child_alias.md");
    let fixture = crate::cli::read_mdtest(&path).expect("recursive child fixture");
    let source = fixture.click_source.as_deref().expect("Click source");
    let sources = crate::cli::source_refs(&fixture.c_sources);
    verify_c_sources(source, &sources).expect("unfold/refold through an equal address");
    let expanded = expand_c_claim_source_by_label(source, &sources, "roundtrip.contract")
        .expect("recursive child fold should expand");
    assert!(
        !expanded.contains("MemoryLoad") && !expanded.contains("__click_"),
        "{expanded}"
    );
    verify_c_sources(&expanded, &sources).expect("expanded fold independently verifies");
}

#[test]
fn pointer_read_single_store_normalization_expands_and_rechecks() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/egraph_pointer_read_single_store.md");
    let fixture = crate::cli::read_mdtest(&path).expect("single-store fixture");
    let source = fixture.click_source.as_deref().expect("Click source");
    let sources = crate::cli::source_refs(&fixture.c_sources);
    verify_c_sources(source, &sources).expect("ordinary pointer claim verifies");
    let expanded = expand_c_claim_source_by_label(source, &sources, "touch.contract")
        .expect("single-store pointer claim expands");
    verify_c_sources(&expanded, &sources).expect("expanded claim independently rechecks");
    let mut changed_sources = fixture.c_sources.clone();
    changed_sources[0].1 = changed_sources[0].1.replace("p->tag = 1", "p->left = 0");
    let changed = crate::cli::source_refs(&changed_sources);
    assert!(
        verify_c_sources(&expanded, &changed).is_err(),
        "a write to the pointer field cannot reuse sibling-write equality"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn recursive_child_sibling_write_fold_expands_and_rechecks() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/egraph_recursive_child_sibling_write.md");
    let fixture = crate::cli::read_mdtest(&path).expect("sibling-write fixture");
    let source = fixture.click_source.as_deref().expect("Click source");
    let sources = crate::cli::source_refs(&fixture.c_sources);
    verify_c_sources(source, &sources).expect("unfold/write/refold verifies");
    let expanded = expand_c_claim_source_by_label(source, &sources, "roundtrip.contract")
        .expect("sibling-write fold expands");
    verify_c_sources(&expanded, &sources).expect("expanded sibling-write fold rechecks");
    let mut changed_sources = fixture.c_sources.clone();
    changed_sources[0].1 = changed_sources[0].1.replace("p->tag = 1", "p->left = 0");
    assert!(verify_c_sources(&expanded, &crate::cli::source_refs(&changed_sources)).is_err());
}

/// A declaration is a name followed by `(` outside every brace. A use of the
/// same name inside a body, even an earlier one, is not the declaration.
#[test]
fn a_declaration_position_skips_uses_inside_bodies() {
    let source = "contract void Shape(int32* p) {\n    owns p[0..1];\n}\n\ntheorem uses() {\n    ensures Shape(&f) by { close(); }\n}\n\n  int32 f(int32* p) {\n    ensures result == 0;\n}\n";
    let position =
        |name| click_declaration_source_position(source, name).map(|at| (at.line, at.column));
    assert_eq!(position("Shape"), Some((1, 1)));
    assert_eq!(position("uses"), Some((5, 1)));
    assert_eq!(position("f"), Some((9, 3)));
    assert_eq!(position("missing"), None);
}

#[test]
fn a_parsed_source_index_holds_only_proof_blocks() {
    let source = "spec enum Mode {\n    Off,\n    On(int32),\n}\n\nresource mode_at(p: int32*) {\n    field model: Mode;\n    match model {\n        Mode::Off => { fact p == 0; },\n        Mode::On(count) => { fact count > 0; },\n    }\n}\n\ntheorem t() {\n    ensures true by { close(); }\n}\n";
    let index = ProofSourceIndex::new(source).unwrap();
    // A resource `match` arm is braced like a proof arm but is not one.
    assert!(index.starts_on_line(9).is_empty());
    assert!(index.starts_on_line(10).is_empty());
    assert_eq!(index.starts_on_line(15).len(), 1);
}

#[test]
fn trace_source_index_preserves_nested_locations_and_containment() {
    let source = "// αβ UTF-8\nresource cell(p: int32*) { owns *p; }\nvoid f(int32* p) {\n    owns r: cell(p);\n} by {\n  have true by { with(cell(p)) { close(); } }\n  if true { normalize(); } else { close(); }\n  cases { true => { step(); } false => { normalize(); } }\n  all { true => { normalize(); } true => { close(); } }\n  outcomes { threw => { step(); } returned => { close(); } }\n  branch ensuring { fact true; } { true => { step(); } false => { close(); } }\n  normalize();\n}\n";
    let index = ProofSourceIndex::new(source).unwrap();
    // A `branch` shares its line only with its own arms' tactics, which are
    // inside it, so the line names it alone.
    let branch = position_at_offset(source, source.find("branch").unwrap());
    let branch_else = position_at_offset(source, source.rfind("close").unwrap());
    let last = position_at_offset(source, source.rfind("normalize").unwrap());
    assert!(!index.line_has_multiple_starts(&branch).unwrap());
    assert!(!index.line_has_multiple_starts(&last).unwrap());
    assert_eq!(
        index.arm_containing(&branch, &branch_else).unwrap(),
        Some(1)
    );
    assert_eq!(index.arm_containing(&branch, &last).unwrap(), None);
    let have = position_at_offset(source, source.find("have").unwrap());
    assert_eq!(
        index.nested_position(&have, &[0, 0]).unwrap(),
        position_at_offset(source, source.find("close").unwrap())
    );
    // Each second arm's first tactic.
    for (kind, inner) in [
        ("if", "close(); }\n  cases"),
        ("cases", "normalize(); } }\n  all"),
        ("all", "close(); } }\n  outcomes"),
    ] {
        let outer = position_at_offset(source, source.find(kind).unwrap());
        assert_eq!(
            index.nested_position(&outer, &[1, 0]).unwrap(),
            position_at_offset(source, source.find(inner).unwrap())
        );
    }
}

#[test]
fn trace_source_index_preserves_unicode_and_implicit_proof_columns() {
    // `by T();` is read as the block `by { T(); }`: both spellings answer
    // every query alike.
    let answers = |proof: &str| {
        let source = &format!("theorem t() {{\n    /* αβ */ ensures true {proof}\n}}\n");
        let spans = parser::parsed_source_spans(source, parser::ProgramLayouts::default()).unwrap();
        let index = ProofSourceIndex::build(source, &spans).unwrap();
        let have = position_at_offset(source, source.find("have").unwrap());
        let child = index.nested_position(&have, &[0]).unwrap();
        assert_eq!(
            child,
            position_at_offset(source, source.find("normalize").unwrap())
        );
        (
            index.have_body_contains(&have, &child).unwrap(),
            index.line_has_multiple_starts(&have).unwrap(),
            index.line_has_multiple_starts(&child).unwrap(),
        )
    };
    assert_eq!(
        answers("by { have true by normalize(); close(); }"),
        answers("by { have true by { normalize(); } close(); }")
    );
}

// A theorem that executes a function names it with a head of its own, which
// a scan of the source for `f(` read as the function. The parser records
// each declaration where it read it.
#[test]
fn a_function_is_located_by_its_own_head_not_an_executing_theorem() {
    let source = r#"verifying "fee.c";
theorem evaluation() executes evaluate(int32 at_size) {
    ensures result == 0;
}
int32 evaluate(int32 at_size) {
    ensures result == 0;
} by { step_until(function.exit); close(); }
"#;
    let tokens = plain_source_tokens(source).unwrap();
    let function = parsed_function_body(source, "evaluate").unwrap();
    assert_eq!(tokens[function.body_close + 1].text, "by");
    assert_eq!(tokens[function.body_open - 1].text, ")");
    // `int32 evaluate(int32 at_size) {`, not the theorem's `executes` head.
    assert_eq!(tokens[function.body_open - 5].text, "evaluate");
    assert_eq!(tokens[function.body_open - 6].text, "int32");
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/surface/expansion/tests.rs");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_15")]
fn named_applications_are_simple_with_ordinary_obligations() {
    let source = r#"
        import click::integer;
        theorem unconditional(x: int32) { ensures x == x by close(); }
        theorem conditional(x: int32) { requires x == 0; ensures x == 0 by close(); }
        theorem value_identity(z: Integer) { ensures z == z by close(); }
        theorem computed(x: int64) {
            requires defined(x + 1i64);
            ensures to_integer(x + 1i64) == to_integer(x + 1i64) by {
                apply(value_identity(to_integer(x + 1i64)));
            }
        }
        theorem client(x: int32) {
            requires x == 0;
            ensures x == 0 by {
                apply(unconditional(x));
                apply(conditional(x));
            }
        }
    "#;
    let sites = c_smart_tactic_source_sites(source, &[]).unwrap();
    assert!(sites.iter().all(|site| {
        site.claim_label != "client.ensures_0" && site.claim_label != "computed.ensures_0"
    }));
    verify_c_sources(source, &[]).unwrap();
    assert!(verify_c_sources(&source.replace("requires defined(x + 1i64);", ""), &[]).is_err());
    assert!(
        verify_c_sources(
            &source.replace(
                "requires x == 0;\n            ensures",
                "requires x == 1;\n            ensures"
            ),
            &[]
        )
        .is_err()
    );
}

#[test]
fn qualified_c_contract_source_locations_preserve_file_aliases() {
    let source = "verifying \"first.c\" as first;\nverifying \"second.c\" as second;\nint32 first::helper() { ensures result == 1; }\nint32 second::helper() { ensures result == 2; }\n";
    let tokens = plain_source_tokens(source).unwrap();
    for (name, line) in [("first::helper", 3), ("second::helper", 4)] {
        let found = parsed_function_body(source, name).unwrap();
        assert_eq!(
            position_at_offset(source, tokens[found.body_open].span.start).line,
            line
        );
        assert_eq!(
            click_declaration_source_position(source, name),
            Some(SourcePosition::new(line, 1))
        );
    }
}

#[test]
fn a_rust_verifying_alias_does_not_change_path_identity() {
    let source =
        "verifying \"first.rs\" as first; fn first::helper() -> i32 { ensures result == 1; }";
    let name = crate::languages::rust::names::path_name(&["first", "helper"]);
    assert!(parsed_function_body(source, &name).is_ok());
}

#[test]
fn rust_integer_literal_spans_keep_later_declarations_addressable() {
    let source = "verifying \"arrays.rs\";\n\
        fn before(bytes: &[u8; 0x4usize]) -> usize {\n\
            requires 0b1_00usize == 4_usize;\n\
            ensures result == 4_usize;\n\
        }\n\
        fn length(words: &[u32; 1 + 2]) -> usize {\n\
            ensures result == 0o3usize;\n\
        }\n";
    let tokens = parser::source_tokens(source).unwrap();
    for literal in ["0x4usize", "0b1_00usize", "4_usize", "0o3usize"] {
        let written = source
            .match_indices(literal)
            .map(|(offset, _)| offset)
            .collect::<Vec<_>>();
        let found = tokens
            .iter()
            .filter(|token| token.text == literal)
            .collect::<Vec<_>>();
        assert_eq!(
            found.len(),
            written.len(),
            "missing literal span: {literal}"
        );
        for (token, offset) in found.into_iter().zip(written) {
            assert_eq!(token.span, offset..offset + literal.len());
            assert_eq!(token.start, position_at_offset(source, offset));
        }
    }
    for name in ["before", "length"] {
        let declaration = source.find(&format!("fn {name}(")).unwrap();
        let open = declaration + source[declaration..].find('{').unwrap();
        let body = parsed_function_body(source, name).unwrap();
        assert_eq!(tokens[body.body_open].span.start, open);
    }
}

#[test]
fn source_tools_share_parser_tokens_and_byte_spans() {
    let source = "/* λ # } */ import click::list::{append}; caller::{closure#12}; Box::(lambda#3); 37u64 -> value => next;";
    let tokens = parser::source_tokens(source).unwrap();
    assert_eq!(
        tokens
            .iter()
            .map(|token| token.text.as_str())
            .collect::<Vec<_>>(),
        [
            "import",
            "click",
            "::",
            "list",
            "::",
            "{",
            "append",
            "}",
            ";",
            "caller",
            "::",
            "{closure#12}",
            ";",
            "Box",
            "::",
            "(lambda#3)",
            ";",
            "37u64",
            "->",
            "value",
            "=>",
            "next",
            ";"
        ]
    );
    for token in tokens {
        assert_eq!(&source[token.span], token.text);
    }
    let invalid = "# a comment the parser refuses\ntheorem t() {}";
    assert!(parser::parse(invalid).is_err());
    assert!(ProofSourceIndex::new(invalid).is_err());
    assert!(verifying_source_paths(invalid).is_err());
}

#[test]
fn source_spelling_uses_tokens_for_shadowing_imports_and_literals() {
    let name = "click::integer::multiply_add";
    let replacement = format!("apply({name}(x));");
    // A file declaration of a selectively imported name is the clash the
    // parser refuses, so the text keeps its full path; a commented one is
    // no declaration.
    for source in [
        "import click::integer::{multiply_add};\n/* banner */ theorem multiply_add(x: Integer) {}",
        "import click::integer::{multiply_add};\ntheorem other() {} theorem multiply_add(x: Integer) {}",
        "import click::integer::{multiply_add};\ntheorem\n multiply_add(x: Integer) {}",
    ] {
        assert_eq!(
            printing::spell_source_names(source, &replacement),
            replacement
        );
    }
    let context = "/* ; # } */ import /* ; */ click::list::{append_cons};";
    let text = "apply(click::list::append_cons(x, xs, ys)); // click::list::append_cons\nverifying \"click::list::append_cons\";";
    assert_eq!(
        printing::spell_source_names(context, text),
        "apply(append_cons(x, xs, ys)); // click::list::append_cons\nverifying \"click::list::append_cons\";"
    );
    let context =
        "import click::integer::{multiply_add};\n// theorem multiply_add\ntheorem client() {}";
    assert_eq!(
        printing::spell_source_names(context, &replacement),
        "apply(multiply_add(x));"
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_15")]
fn commented_selective_and_qualified_names_expand_and_recheck() {
    let source = r#"
/* # ; theorem fake() {} */
import /* ; */ click::list::{append, append_left_identity};
theorem client(xs: List<int32>) {
    ensures append(List<int32>::Nil, xs) == xs by {
        apply(click::list::append_left_identity(xs));
    }
}
"#;
    verify_c_sources(source, &[]).unwrap();
    let expanded = expand_c_claim_source_by_label(source, &[], "client.ensures_0").unwrap();
    verify_c_sources(&expanded, &[]).unwrap();
    assert!(expanded.contains("/* # ; theorem fake() {} */"));
    assert!(
        verify_c_sources(&expanded.replace("== xs by", "== List<int32>::Nil by"), &[]).is_err()
    );
}

#[test]
fn resource_and_theorem_name_namespaces_roundtrip_with_commented_imports() {
    let markdown = mdtest_markdown("source_name_spelling_uses_parser_bindings.md");
    let source = markdown
        .split("```click\n")
        .nth(1)
        .unwrap()
        .split("```")
        .next()
        .unwrap();
    let sources = [("keep.c", "void keep(int32* p) { }")];
    verify_c_sources(source, &sources).unwrap();
    for label in [
        "client.ensures_0",
        "keep.contract",
        "int32_positive_is_nonnegative.ensures_0",
    ] {
        let expanded = expand_c_claim_source_by_label(source, &sources, label).unwrap();
        verify_c_sources(&expanded, &sources).unwrap();
    }
}

#[test]
fn branch_transfers_cannot_claim_an_unreachable_return() {
    use crate::kernel::{program_if, program_return, program_seq, program_skip};
    let branch = |body| {
        program_if(
            crate::kernel::program_expression::int32_literal(1),
            body,
            program_skip(),
        )
    };
    assert!(
        returning_then_arms(&branch(program_return(
            crate::kernel::program_expression::int32_literal(0)
        )))
        .contains(&0)
    );
    assert!(
        returning_then_arms(&branch(program_seq(
            program_skip(),
            program_return(crate::kernel::program_expression::int32_literal(0))
        )))
        .contains(&0)
    );
    for transfer in [
        ProgramStatement::Break,
        ProgramStatement::Continue,
        ProgramStatement::Goto {
            target: crate::kernel::ControlTargetId(7),
            exited_locals: Default::default(),
        },
        ProgramStatement::Throw(crate::kernel::program_expression::int32_literal(0)),
    ] {
        assert!(
            returning_then_arms(&branch(program_seq(
                transfer,
                program_return(crate::kernel::program_expression::int32_literal(0))
            )))
            .is_empty()
        );
    }
}

#[test]
fn a_caught_call_can_bypass_its_branch_return() {
    use crate::kernel::{program_if, program_return, program_seq, program_skip};
    let body = program_if(
        crate::kernel::program_expression::int32_literal(1),
        program_seq(
            ProgramStatement::Call {
                function_name: "may_throw".into(),
                arguments: Vec::new(),
                callee: None,
            },
            program_return(crate::kernel::program_expression::int32_literal(0)),
        ),
        program_skip(),
    );
    assert!(returning_then_arms(&body).contains(&0));
    let caught = ProgramStatement::TryCatchInt32 {
        try_body: Box::new(body),
        binding: "error".into(),
        handler: Box::new(program_skip()),
    };
    assert!(
        returning_then_arms(&caught).is_empty(),
        "a handler may continue after the if without returning"
    );
}

/// A cited fact recovered at the function's entry is spelled with its
/// constants unanchored: `at(function.entry, -9223372036854775808)` reads
/// the `int64` minimum as a C numeral, which the rechecked certificate
/// would not find.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn an_solve_sum_identity_after_a_proved_lower_bound_reverifies() {
    let c_source = "#include <stdint.h>\nint64_t inc(int64_t q) { return q; }\n";
    let source = r#"verifying "inc.c";

int64 inc(int64 q) {
    requires to_integer(q) <= 9223372036854775806;
    ensures true;
} by {
    have -9223372036854775808 <= to_integer(q);
    have defined(q + 1i64) by close();
    have to_integer(q + 1i64) == to_integer(q) + 1;
    step_until(function.exit);
    close();
}
"#;
    let sources = [("inc.c", c_source)];
    let expanded = expand_c_claim_source_by_label(source, &sources, "inc.contract")
        .expect("the sum identity expands");
    assert!(
        !expanded.contains("at(function.entry, -9223372036854775808)"),
        "{expanded}"
    );
    verify_c_sources(&expanded, &sources).expect("the expansion verifies");
}

/// A written script that stops with C left ends in the implicit tail, which
/// is selected at the script's closing brace: expanding it writes the tail's
/// steps and splits after the last written tactic. It is not in the static
/// inventory, since whether it has work is known only once the proof runs.
/// With the implicit closer off, as an expansion is checked cold, the tail
/// runs no C, so the original script is refused.
#[test]
fn a_written_scripts_implicit_tail_is_an_expansion_site() {
    let c_source = "int32 f(int32 x) { int32 y = x; if (x < 0) { return 0; } return y; }";
    let sources = [("f.c", c_source)];
    let click_source = r#"verifying "f.c";
int32 f(int32 x) {
    ensures result >= 0 or x < 0;
} by {
    step();
}
"#;
    assert!(
        c_smart_tactic_source_sites(click_source, &sources)
            .unwrap()
            .is_empty()
    );
    let expanded = expand_c_tactic_source_at(click_source, &sources, 6, 1).unwrap();
    assert!(
        expanded.contains("    step();\n    step();\n    if "),
        "{expanded}"
    );
    verify_c_sources(&expanded, &sources).expect("the expanded tail should verify");
    let refused = without_implicit_solve(|| verify_c_sources(click_source, &sources))
        .expect_err("with the implicit closer off the tail runs no C");
    assert!(
        refused.message().contains("the implicit tail is off"),
        "{}",
        refused.message()
    );
}

#[test]
fn common_machine_call_expansion_rechecks_selected_call_premises() {
    let source = "function f(x: int32) -> int32 { x } theorem client(x: int32) { requires f(x) == 7; requires defined(f(x) + 1); ensures f(x) + 1 == 8 by { close() using { f(x) == 7; defined(f(x) + 1); } } }";
    verify_c_sources(source, &[]).unwrap();
    let expanded = expand_c_claim_source_by_label(source, &[], "client.ensures_0").unwrap();
    verify_c_sources(&expanded, &[]).unwrap();
    assert!(expanded.contains("f(x)"));
    assert!(verify_c_sources(&expanded.replace("requires f(x) == 7;", ""), &[]).is_err());
    assert!(
        verify_c_sources(
            &expanded.replace("ensures f(x) + 1 == 8", "ensures f(x) + 1 == 9"),
            &[]
        )
        .is_err()
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: aggregate call and conditional results expand and independently recheck"]
fn aggregate_step_result_fields_expand_and_recheck_without_generated_locals() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/aggregate_expression_results_are_named_by_their_source_steps.md");
    let fixture = crate::cli::read_mdtest(&path).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = crate::cli::source_refs(&fixture.c_sources);
    verify_c_sources(source, &sources).expect("aggregate result source proof");
    for label in [
        "call_field.contract",
        "constant_conditional.contract",
        "conditional_field.ensures_0",
    ] {
        let expanded = expand_c_claim_source_by_label(source, &sources, label).expect(label);
        assert!(!expanded.contains("__click_aggregate_result"), "{expanded}");
        verify_c_sources(&expanded, &sources).expect("aggregate result expansion rechecks");
    }
    let changed = fixture
        .c_sources
        .iter()
        .map(|(name, text)| {
            (
                name.clone(),
                text.replace("return make(input).right;", "return make(input).left;"),
            )
        })
        .collect::<Vec<_>>();
    assert!(verify_c_sources(source, &crate::cli::source_refs(&changed)).is_err());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: source literal names expand and independently recheck"]
fn string_literal_source_references_raise_expand_and_recheck() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/string_literal_source_reference.md");
    let fixture = crate::cli::read_mdtest(&path).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = crate::cli::source_refs(&fixture.c_sources);
    verify_c_sources(source, &sources).expect("source literal proof");
    for label in ["text.ensures_0", "text.ensures_1", "first.contract"] {
        let expanded = expand_c_claim_source_by_label(source, &sources, label).expect(label);
        assert!(!expanded.contains("__click_string_literal"), "{expanded}");
        verify_c_sources(&expanded, &sources).expect("literal source expansion");
    }
}

#[test]
fn apply_fact_expands_antecedent_proofs_without_extract_or_search() {
    let source = r#"
        theorem demo(x: int32, y: int32) {
            requires x > 1;
            requires x > 0 implies y > 0;
            ensures y > 0 by {
                have h: x > 0 implies y > 0 by close();
                apply(h);
            }
        }
    "#;
    verify_click_theorems(source).expect("bare fact application proves its antecedent");
    let expanded =
        expand_pure_theorem_source(source, &[], "demo", 0).expect("fact application expands");
    assert!(
        expanded.contains("apply(x > 0 implies y > 0);"),
        "{expanded}"
    );
    assert!(!expanded.contains("extract("), "{expanded}");
    without_implicit_solve(|| verify_click_theorems(&expanded))
        .expect("expanded fact application checks without search");
    for invalid in [
        expanded.replace("requires x > 1;", ""),
        expanded.replace("requires x > 0 implies y > 0;", ""),
    ] {
        assert!(without_implicit_solve(|| verify_click_theorems(&invalid)).is_err());
    }
}

#[test]
fn apply_fact_c_frontier_and_outcome_expansion_rechecks_without_search() {
    let c = "int32 identity(int32 x) { return x; }";
    let template = r#"
        verifying "identity.c";
        int32 identity(int32 x) {
            requires x > 1;
            requires x > 0 implies x != 0;
            ensures result != 0;
        } by { BODY }
    "#;
    for body in [
        "apply(x > 0 implies x != 0); step();",
        "step(); apply(x > 0 implies x != 0);",
    ] {
        let source = template.replace("BODY", body);
        let sources = [("identity.c", c)];
        verify_c_sources(&source, &sources).unwrap_or_else(|error| panic!("{body}: {error}"));
        let expanded = expand_c_claim_source_by_label(&source, &sources, "identity.contract")
            .unwrap_or_else(|error| panic!("{body}: {error}"));
        assert!(
            expanded.contains("apply(x > 0 implies x != 0);"),
            "{expanded}"
        );
        without_implicit_solve(|| verify_c_sources(&expanded, &sources))
            .unwrap_or_else(|error| panic!("{body}: {error}\n{expanded}"));
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_15")]
fn solve_expands_disjunction_projection_to_cases_without_extract() {
    let source = r#"
        theorem demo(x: int32, y: int32) {
            requires (x > 0 and y == 1) or ((x > 0 and y == 2) or (x > 0 and y == 3));
            ensures x > 0 by close();
        }
    "#;
    verify_click_theorems(source).unwrap();
    let expanded = expand_pure_theorem_source(source, &[], "demo", 0).unwrap();
    assert!(expanded.contains("cases {"), "{expanded}");
    assert!(!expanded.contains("extract("), "{expanded}");
    assert!(!expanded.contains("solve()"), "{expanded}");
    without_implicit_solve(|| verify_click_theorems(&expanded)).unwrap();
    let invalid = expanded.replace("x > 0 and y == 3", "x < 0 and y == 3");
    assert!(without_implicit_solve(|| verify_click_theorems(&invalid)).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_15")]
fn solve_expands_propagated_partial_implication_to_known() {
    let source = r#"
        theorem demo(x: int32, y: int32, z: int32) {
            requires x > 0;
            requires x > 0 implies y > 0 implies z > 0;
            ensures y > 0 implies z > 0 by close();
        }
    "#;
    verify_click_theorems(source).unwrap();
    let expanded = expand_pure_theorem_source(source, &[], "demo", 0).unwrap();
    assert!(expanded.contains("close()"), "{expanded}");
    assert!(!expanded.contains("extract("), "{expanded}");
    assert!(!expanded.contains("solve()"), "{expanded}");
    without_implicit_solve(|| verify_click_theorems(&expanded)).unwrap();
    let missing = expanded.replace("requires x > 0;", "");
    assert!(without_implicit_solve(|| verify_click_theorems(&missing)).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_16")]
fn solve_expands_excluded_middle_to_if_without_extract() {
    let source = "theorem demo(make: Bool) { ensures make or not make by close(); }";
    verify_click_theorems(source).unwrap();
    let expanded = expand_pure_theorem_source(source, &[], "demo", 0).unwrap();
    assert!(expanded.contains("if make"), "{expanded}");
    assert!(!expanded.contains("extract("), "{expanded}");
    without_implicit_solve(|| verify_click_theorems(&expanded)).unwrap();
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: memory disjunction expansion and cold replay"]
fn solve_expands_refuted_memory_disjunction_without_extract() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/sequence-transform");
    let source = std::fs::read_to_string(root.join("sequence_transform.click")).unwrap();
    let c = std::fs::read_to_string(root.join("sequence_transform.c")).unwrap();
    let sources = [("sequence_transform.c", c.as_str())];
    verify_c_sources(&source, &sources).unwrap();
    let expanded =
        expand_c_claim_source_by_label(&source, &sources, "sequence_contains3.ensures_1").unwrap();
    assert!(!expanded.contains("extract("), "{expanded}");
    without_implicit_solve_for_claim("sequence_contains3.contract", || {
        verify_c_sources(&expanded, &sources).map_err(|error| error.to_string())
    })
    .unwrap();
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: loop exit projection expansion and cold replay"]
fn solve_expands_loop_exit_projection_without_extract() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/authority_loop_exit_disjunction_ignores_a_closed_guard.md");
    let fixture = crate::cli::read_mdtest(&path).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c_sources(source, &sources).unwrap();
    let expanded = expand_c_claim_source_by_label(source, &sources, "paint.contract").unwrap();
    assert!(!expanded.contains("extract("), "{expanded}");
    without_implicit_solve_for_claim("paint.contract", || {
        verify_c_sources(&expanded, &sources).map_err(|error| error.to_string())
    })
    .unwrap();
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: C declaration references expand and independently recheck"]
fn c_declaration_references_raise_expand_and_recheck() {
    for (fixture, label) in [
        ("c_declaration_references", "identity.contract"),
        ("c_aggregate_declaration_references", "read_item.contract"),
        ("c_static_declaration_references", "read.contract"),
        ("c_static_declaration_references", "read_cell.contract"),
        ("c_static_declaration_references", "file_read.contract"),
        (
            "nested_field_aliases_keep_post_call_scalar_reads",
            "cleanup.contract",
        ),
    ] {
        let path =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("mdtests/{fixture}.md"));
        let fixture = crate::cli::read_mdtest(&path).unwrap();
        let source = fixture.click_source.as_deref().unwrap();
        let sources = crate::cli::source_refs(&fixture.c_sources);
        verify_c_sources(source, &sources).expect("declaration reference proof");
        let expanded = expand_c_claim_source_by_label(source, &sources, label).unwrap();
        assert!(!expanded.contains("#scope"), "{expanded}");
        assert!(!expanded.contains("#static"), "{expanded}");
        assert!(!expanded.contains("#file-static"), "{expanded}");
        verify_c_sources(&expanded, &sources).expect("declaration reference expansion");
    }
}

#[test]
fn ordinary_fold_unfold_expands_with_replayable_guard_proofs() {
    let source = r#"
function tally(lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + 1 })
}
theorem append_tally(lo: int32, hi: int32) {
    requires 0 <= lo;
    requires lo < hi;
    ensures tally(lo, hi) == tally(lo, hi - 1) + 1 by {
        unfold(tally(lo, hi));
        normalize();
    }
}
"#;
    let expanded = expand_c_claim_source_by_label(source, &[], "append_tally.ensures_0")
        .expect("ordinary unfolding proves its fold guards");
    crate::surface::proof::without_implicit_solve(|| verify_c_sources(&expanded, &[]))
        .expect("the generated guard proofs replay without search");
    let invalid = expanded.replacen(
        "ensures tally(lo, hi) == tally(lo, hi - 1) + 1",
        "ensures tally(lo, hi) == tally(lo, hi - 1) + 2",
        1,
    );
    assert_ne!(expanded, invalid);
    crate::surface::proof::without_implicit_solve(|| verify_c_sources(&invalid, &[]))
        .expect_err("a different last-step value must be rejected");
}

#[test]
fn ordinary_fold_cases_expand_and_replay_without_implicit_solving() {
    for source in [
        r#"
function tally(end: int32) -> Integer { (0..end).fold(0, |acc, k| { acc + 1 }) }
theorem fold_case(end: int32) {
    requires end <= 0;
    ensures tally(end) == 0 by {
        unfold(tally(end));
        normalize();
    }
}
"#,
        r#"
function tally(lo: int32, hi: int32) -> Integer { (lo..hi).fold(0, |acc, k| { acc + 1 }) }
theorem fold_case(lo: int32, hi: int32) {
    requires lo <= hi;
    requires hi < 2147483647;
    ensures tally(lo, hi + 1) == tally(lo, hi) + 1 by {
        unfold(tally(lo, hi + 1));
        close();
    }
}
"#,
        r#"
function tally(lo: uint64, hi: uint64) -> Integer { (lo..hi).fold(0, |acc, k| { acc + 1 }) }
theorem fold_case(lo: uint64, hi: uint64) {
    requires lo <= hi;
    requires hi < 18446744073709551615u64;
    ensures tally(lo, hi + 1u64) == tally(lo, hi) + 1 by {
        unfold(tally(lo, hi + 1u64));
        close();
    }
}
"#,
        r#"
function tally(step: fn(Integer, Integer) -> Integer, lo: Integer, hi: Integer) -> Integer {
    (lo..hi).fold(0, step)
}
theorem fold_case(lo: Integer, hi: Integer) {
    requires lo <= hi;
    ensures tally(|acc: Integer, k: Integer| -> Integer { acc + k }, lo, hi + 1)
        == tally(|acc: Integer, k: Integer| -> Integer { acc + k }, lo, hi) + hi by {
        have hi + 1 - 1 == hi by close();
        have lo <= hi + 1 - 1 by close();
        have tally(|acc: Integer, k: Integer| -> Integer { acc + k }, lo, hi + 1)
            == tally(|acc: Integer, k: Integer| -> Integer { acc + k }, lo, hi) + hi by {
            unfold(tally(|acc: Integer, k: Integer| -> Integer { acc + k }, lo, hi + 1));
            close();
        }
        close();
    }
}
"#,
    ] {
        let expanded = expand_c_claim_source_by_label(source, &[], "fold_case.ensures_0")
            .expect("ordinary fold should expand");
        assert!(expanded.contains("unfold(tally("), "{expanded}");
        crate::surface::proof::without_implicit_solve(|| verify_c_sources(&expanded, &[]))
            .expect("ordinary unfold must replay using the established guards");
        // Expanding an expanded certificate must keep the ordinary form.
        let repeated = expand_c_claim_source_by_label(&expanded, &[], "fold_case.ensures_0")
            .expect("ordinary expansion should remain expandable");
        assert!(repeated.contains("unfold(tally("), "{repeated}");
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_16")]
fn ordinary_fold_expansion_requires_the_empty_range_guard() {
    let source = r#"
function tally(end: int32) -> Integer { (0..end).fold(0, |acc, k| { acc + 1 }) }
theorem fold_case(end: int32) {
    requires end <= 0;
    ensures tally(end) == 0 by {
        unfold(tally(end));
        normalize();
    }
}
"#;
    let expanded = expand_c_claim_source_by_label(source, &[], "fold_case.ensures_0").unwrap();
    let invalid = expanded.replacen("requires end <= 0;", "requires end <= 1;", 1);
    assert_ne!(invalid, expanded);
    crate::surface::proof::without_implicit_solve(|| verify_c_sources(&invalid, &[]))
        .expect_err("unfold cannot retain the empty law without its range guard");
    let nested = source.replace(
        "unfold(tally(end));\n        normalize();",
        "have tally(end) == 0 by { unfold(tally(end)); close(); }\n        close();",
    );
    assert_ne!(nested, source);
    let position = position_at_offset(&nested, nested.find("have tally").unwrap());
    let selected = expand_c_tactic_source_at(&nested, &[], position.line, position.column)
        .expect("a selected smart have expands its nested fold");
    assert!(selected.contains("unfold(tally(end));"), "{selected}");
    crate::surface::proof::without_implicit_solve(|| verify_c_sources(&selected, &[]))
        .expect("selected expansion replays without implicit solving");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_16")]
fn ordinary_fold_expansion_keeps_array_reads_at_the_execution_frontier() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/unfold_fold_function_appends_last_cell.md");
    let fixture = crate::cli::read_mdtest(&path).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = crate::cli::source_refs(&fixture.c_sources);
    let expanded =
        expand_c_claim_source_by_label(source, &sources, "prefix_sum_equation.ensures_0").unwrap();
    assert!(expanded.contains("unfold(icount(a, 0, n));"), "{expanded}");
    without_implicit_solve_for_claim("prefix_sum_equation.ensures_0", || {
        verify_c_sources(&expanded, &sources).map_err(|error| error.to_string())
    })
    .expect("the memory-reading fold and its guard proofs replay without search");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_16")]
fn ordinary_fold_expansion_in_both_replays_without_implicit_solving() {
    let source = r#"
function tally(end: int32) -> Integer { (0..end).fold(0, |acc, k| { acc + 1 }) }
theorem fold_case(end: int32) {
    requires end <= 0;
    ensures tally(end) == 0 and 0 <= tally(end) by {
        all {
            tally(end) == 0 => {
                unfold(tally(end));
                normalize();
            }
            0 <= tally(end) => {
                unfold(tally(end));
                normalize();
            }
        }
    }
}
"#;
    let expanded = expand_c_claim_source_by_label(source, &[], "fold_case.ensures_0").unwrap();
    crate::surface::proof::without_implicit_solve(|| verify_c_sources(&expanded, &[]))
        .expect("both checked branches replay with ordinary unfolds");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by expansion_api_batch_16")]
fn exact_proposition_propagation_replays_without_search() {
    let source = r#"
        theorem propagated(a: int32, b: int32) {
            requires a == 0 or b == 0;
            requires not (a == 0);
            ensures b == 0 by close();
        }
    "#;
    verify_click_theorems(source).expect("solver uses propagated fact");
    let expanded = expand_pure_theorem_source(source, &[], "propagated", 0)
        .expect("propagated closure expands");
    assert!(expanded.contains("close()"), "{expanded}");
    without_implicit_solve(|| verify_click_theorems(&expanded))
        .expect("exact propagation needs no solver");
    for invalid in [
        expanded.replace("requires a == 0 or b == 0;", ""),
        expanded.replace("requires not (a == 0);", ""),
    ] {
        assert!(without_implicit_solve(|| verify_click_theorems(&invalid)).is_err());
    }
}

#[test]
fn heap_free_borrow_separation_expands_and_rechecks() {
    let c = r#"
void release(unsigned char *p, unsigned long n, int32 *q) {
    free(p);
}
"#;
    let proof = r#"
verifying "free_borrow.c";

void release(uint8* p, uint64 n, int32* q) {
    requires p != 0;
    requires 1u64 <= n and n <= 1000u64;
    consumes allocation(p, n);
    consumes p[0..n];
    views *q;
} by { step() by { close(); } }
"#;
    let sources = [("free_borrow.c", c)];
    verify_c_sources(proof, &sources).unwrap_or_else(|error| panic!("{}", error.report()));
    let expanded = expand_c_claim_source_by_label(proof, &sources, "release.contract").unwrap();
    without_implicit_solve_for_claim("release.contract", || {
        verify_c_sources(&expanded, &sources).map_err(|error| error.report())
    })
    .unwrap();
}

#[test]
fn aggregate_copy_borrow_separation_expands_and_rechecks() {
    let c = r#"
union Payload { int32 value; };
struct Packet { int32 tag; union Payload payload; };
void copy(struct Packet *dst, struct Packet *src, int32 *q) {
    *dst = *src;
}
"#;
    let proof = r#"
verifying "copy_borrow.c";
void copy(struct Packet* dst, struct Packet* src, int32* q) {
    owns dst->tag;
    owns dst->payload.value;
    owns src->tag;
    owns src->payload.value;
    views *q;
    requires separate(memory((dst as (uint8*))[0..8]), memory(*q));
} by { step() by { close(); } }
"#;
    let sources = [("copy_borrow.c", c)];
    verify_c_sources(proof, &sources).unwrap_or_else(|error| panic!("{}", error.report()));
    let expanded = expand_c_claim_source_by_label(proof, &sources, "copy.contract").unwrap();
    without_implicit_solve_for_claim("copy.contract", || {
        verify_c_sources(&expanded, &sources).map_err(|error| error.report())
    })
    .unwrap();

    // The borrow can alias the second member when the separation is absent.
    let missing = proof.replace(
        "requires separate(memory((dst as (uint8*))[0..8]), memory(*q));",
        "",
    );
    assert!(
        without_proof_search_for_claim("copy.contract", || {
            verify_c_sources(&missing, &sources).map_err(|error| error.report())
        })
        .is_err()
    );
}
