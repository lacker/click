use super::*;

#[test]
fn location_verification_skips_unrelated_function_proofs() {
    let good_c = r#"
int32 good(int32 x) {
    return x;
}
"#;
    let bad_c = r#"
int32 bad(int32 x) {
    return x;
}
"#;
    let click_source = r#"
verifying "good.c";
verifying "bad.c";

int32 good(int32 x) {
    ensures result == x;
} by {
    execute();
    simp();
}

int32 bad(int32 x) {
    ensures result == x + 1;
} by {
    execute();
    simp();
}
"#;
    let sources = [("good.c", good_c), ("bad.c", bad_c)];
    let selected = click_source.find("ensures result == x;").unwrap();
    let position = expansion::position_at_offset(click_source, selected);

    verify_c0_sources(click_source, &sources)
        .expect_err("complete verification should reject the bad function");
    let verified = verify_c0_sources_at(click_source, &sources, position.line, position.column)
        .expect("location verification should skip the unrelated bad proof");
    assert!(
        verified
            .iter()
            .all(|theorem| theorem.function_block.signature().name() == "good")
    );
}

#[test]
fn location_verification_checks_called_function_dependencies() {
    let callee_c = r#"
int32 callee(int32 x) {
    return x;
}
"#;
    let caller_c = r#"
int32 caller(int32 x) {
    int32 result;
    result = callee(x);
    return result;
}
"#;
    let click_source = r#"
verifying "callee.c";
verifying "caller.c";

int32 callee(int32 x) {
    ensures result == x + 1;
} by {
    execute();
    simp();
}

int32 caller(int32 x) {
    ensures result == x + 1;
} by {
    execute();
    simp();
}
"#;
    let sources = [("callee.c", callee_c), ("caller.c", caller_c)];
    let caller_proof = click_source.rfind("execute()").unwrap();
    let position = expansion::position_at_offset(click_source, caller_proof);

    let error = verify_c0_sources_at(click_source, &sources, position.line, position.column)
        .expect_err("targeted caller verification must check its callee dependency");
    assert!(error.message().contains("callee"), "{}", error.message());
}

#[test]
fn tactic_expansion_loads_callees_after_the_selected_source_tactic() {
    let sources = [
        ("first.c", "int32 first(int32 x) { return x; }"),
        ("later.c", "int32 later(int32 x) { return x; }"),
        (
            "caller.c",
            "int32 caller(int32 x) { int32 a = first(x); int32 b = later(x); return a + b; }",
        ),
    ];
    let click_source = r#"
verifying "first.c";
verifying "later.c";
verifying "caller.c";

int32 first(int32 x) { ensures result == x; } by simp;
int32 later(int32 x) { ensures result == x; } by simp;
int32 caller(int32 x) { ensures result == x + x; } by {
    step();
    step();
    execute();
    simp();
}
"#;
    let source_map = sources.iter().copied().collect::<BTreeMap<_, _>>();
    let file = parse_c0_click_file(click_source, &sources).unwrap();
    let parsed = parse_verified_sources(&file, &source_map).unwrap();
    let required = tactic_expansion_required_functions(
        &file,
        &parsed,
        (
            ProofSite::FunctionClaim {
                function_name: "caller".to_string(),
                claim: CProofClaim::Grouped,
            },
            Some(0),
        ),
    )
    .unwrap();

    assert_eq!(
        required,
        BTreeSet::from([
            "caller".to_string(),
            "first".to_string(),
            "later".to_string(),
        ])
    );
}

#[test]
fn modular_call_snapshot_anchor_replays_with_owned_resource() {
    let init_c = r#"
struct box {
    int32 value;
    int32* data;
};

int32 box_init(struct box* owner, int32 data[], int32 value) {
    owner->value = 0;
    owner->data = data;
    data[0] = 0;
    return 0;
}
"#;
    let read_c = r#"
struct box {
    int32 value;
    int32* data;
};

int32 box_read(struct box* owner) {
    return owner->data[0];
}
"#;
    let set_c = r#"
struct box {
    int32 value;
    int32* data;
};

int32 box_set(struct box* owner, int32 value) {
    int32 index;
    index = owner->value;
    owner->data[index] = value;
    owner->value = index + 1;
    return owner->value;
}
"#;
    let pipeline_c = r#"
struct box {
    int32 value;
    int32* data;
};

int32 box_pipeline(struct box* owner, int32 data[], int32 value) {
    int32 ignored;
    int32 observed;
    ignored = box_init(owner, data, value);
    ignored = box_set(owner, value);
    observed = box_read(owner);
    return observed;
}
"#;
    let click_source = r#"
resource owned_box(owner: struct box*) {
    owns owner->value;
    owns owner->data;
    owns owner->data[0..1];
    fact separate(memory(object(owner)), memory(owner->data[0..1]));
}

verifying "box_init.c";
verifying "box_set.c";
verifying "box_read.c";
verifying "box_pipeline.c";

int32 box_init(struct box* owner, int32 data[], int32 value) {
    requires separate(memory(object(owner)), memory(data[0..1]));
    consumes object(owner);
    consumes data[0..1];
    mutable object(owner), data[0..1];
    produces owned_box(owner);
    ensures owner->data == data;
    ensures owner->value == 0;
} by {
    execute();
    have separate(memory(object(owner)), memory(owner->data[0..1])) by simp;
    fold(owned_box(owner));
    frame();
    simp();
}

int32 box_read(struct box* owner) {
    views owned_box(owner);
    immutable;
    ensures result == owner->data[0] by auto;
}

int32 box_set(struct box* owner, int32 value) {
    requires owner->value == 0;
    owns owned_box(owner);
    mutable owner->value, (owner->data + owner->value)[0..1];
    ensures result == old(owner->value) + 1;
    ensures owner->value == old(owner->value) + 1;
    ensures owner->data[old(owner->value)] == value;
} by {
    unfold(owned_box(owner));
    have owner->value < 2147483647 by simp;
    execute();
    have separate(memory(object(owner)), memory(owner->data[0..1])) by simp;
    fold(owned_box(owner));
    frame();
    simp();
}

int32 box_pipeline(struct box* owner, int32 data[], int32 value) {
    requires separate(memory(object(owner)), memory(data[0..1]));
    consumes object(owner);
    consumes data[0..1];
    produces owned_box(owner);
    ensures result == value;
} by {
    execute_until(statement(3));
    have owner->data == data by simp;
    have owner->value == 0 by simp;
    step() using {
        owner->value == 0;
        loadable(old(object(owner)));
        loadable(old(data[0..1]));
    }
    have owner->data[at(statement(3).entry, owner->value)] == value by {
        assumption();
    }
    have owner->data[0] == value by simp;
    step() using {
        owner->data[0] == value;
        loadable(old(object(owner)));
        loadable(old(data[0..1]));
    }
    execute();
    simp();
}
"#;

    verify_c0_sources(
        click_source,
        &[
            ("box_init.c", init_c),
            ("box_set.c", set_c),
            ("box_read.c", read_c),
            ("box_pipeline.c", pipeline_c),
        ],
    )
    .expect("an explicit call-entry snapshot should replay with an owned resource");
}

/// A `simp() using` premise that equates one expression across two call
/// transitions denotes an available fact only through the kernel's certified
/// snapshot bridge — no single replay-time fact carries that exact spelling.
/// The generated certificate must materialize the bridged spelling with an
/// explicit snapshot transport at construction time; simple `rewrite` replay
/// never searches for an equivalent equality, so a certificate that cites the
/// bridged spelling directly does not replay.
#[test]
fn snapshot_bridged_simp_premise_expands_to_an_explicit_transport() {
    let init_c = r#"
struct box {
    int32 value;
    int32* data;
};

int32 box_init(struct box* owner, int32 data[], int32 value) {
    owner->value = value;
    owner->data = data;
    return 0;
}
"#;
    let touch_c = r#"
struct box {
    int32 value;
    int32* data;
};

int32 box_touch(struct box* owner) {
    owner->value = 1;
    return 0;
}
"#;
    let pipeline_c = r#"
struct box {
    int32 value;
    int32* data;
};

int32 box_pipeline(struct box* owner, int32 data[]) {
    int32 ignored;
    ignored = box_init(owner, data, 0);
    ignored = box_touch(owner);
    ignored = box_touch(owner);
    return 0;
}
"#;
    let click_source = r#"
resource owned_box(owner: struct box*) {
    owns owner->value;
    owns owner->data;
}

verifying "box_init.c";
verifying "box_touch.c";
verifying "box_pipeline.c";

int32 box_init(struct box* owner, int32 data[], int32 value) {
    consumes object(owner);
    mutable object(owner);
    produces owned_box(owner);
    ensures owner->data == data;
    ensures owner->value == value;
} by {
    execute();
    fold(owned_box(owner));
    frame();
    simp();
}

int32 box_touch(struct box* owner) {
    owns owned_box(owner);
    mutable owner->value;
    ensures owner->data == old(owner->data);
} by {
    unfold(owned_box(owner));
    execute();
    fold(owned_box(owner));
    frame();
    simp();
}

int32 box_pipeline(struct box* owner, int32 data[]) {
    consumes object(owner);
    produces owned_box(owner);
    ensures owner->data == data;
} by {
    step();
    step() using {
        loadable(old(object(owner)));
    }
    step() using {
        loadable(old(object(owner)));
        owner->data == data;
    }
    step() using {
        loadable(old(object(owner)));
        owner->data == data;
    }
    have owner->data == data by {
        simp() using {
            owner->data == at(statement(2).entry, owner->data);
            at(statement(2).entry, owner->data) == data;
        }
    }
    step() using {
        owner->data == data;
    }
    simp();
}
"#;
    let sources = [
        ("box_init.c", init_c),
        ("box_touch.c", touch_c),
        ("box_pipeline.c", pipeline_c),
    ];

    verify_c0_sources(click_source, &sources)
        .expect("the snapshot-bridged restricted simp certificate should replay");

    let selected = click_source.find("have owner->data == data by {").unwrap();
    let position = expansion::position_at_offset(click_source, selected);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("the snapshot-bridged restricted simp should expand");
    assert!(
        expanded.contains(
            "transport(at(statement(2).entry, owner->data) == at(statement(2).entry, owner->data), \
             owner->data == at(statement(2).entry, owner->data))"
        ),
        "the certificate must materialize the bridged premise spelling before rewriting:\n{expanded}"
    );
    assert!(
        expanded.contains("rewrite(owner->data == at(statement(2).entry, owner->data));"),
        "the rewrite must cite the construction-time premise spelling:\n{expanded}"
    );
    verify_c0_sources(&expanded, &sources)
        .expect("the explicit bridged-premise certificate should replay");
}

#[test]
fn execute_until_expands_mixed_snapshot_call_postconditions() {
    let zero_c = r#"
struct counter {
    int32 value;
};

int32 zero(struct counter* owner) {
    owner->value = 0;
    return owner->value;
}
"#;
    let increment_c = r#"
struct counter {
    int32 value;
};

int32 increment(struct counter* owner) {
    int32 before;
    before = owner->value;
    owner->value = before + 1;
    return owner->value;
}
"#;
    let pipeline_c = r#"
struct counter {
    int32 value;
};

int32 pipeline(struct counter* owner) {
    int32 ignored;
    ignored = zero(owner);
    ignored = increment(owner);
    return owner->value;
}
"#;
    let click_source = r#"
resource counter(owner: struct counter*) {
    owns owner->value;
}

verifying "zero.c";
verifying "increment.c";
verifying "pipeline.c";

int32 zero(struct counter* owner) {
    consumes object(owner);
    mutable object(owner);
    produces counter(owner);
    ensures result == 0;
    ensures owner->value == 0;
} by {
    execute();
    fold(counter(owner));
    frame();
    simp();
}

int32 increment(struct counter* owner) {
    requires owner->value < 2147483647;
    owns counter(owner);
    mutable owner->value;
    ensures result == old(owner->value) + 1;
    ensures owner->value == old(owner->value) + 1;
} by {
    unfold(counter(owner));
    execute();
    fold(counter(owner));
    frame();
    simp();
}

int32 pipeline(struct counter* owner) {
    consumes object(owner);
    mutable object(owner);
    produces counter(owner);
    ensures result == 1;
    ensures owner->value == 1;
} by {
    execute_until(statement(3));
    have owner->value == 1 by simp;
    step() using {
        owner->value == 1;
    }
    frame();
    simp();
}
"#;
    let sources = [
        ("zero.c", zero_c),
        ("increment.c", increment_c),
        ("pipeline.c", pipeline_c),
    ];

    verify_c0_sources(click_source, &sources).expect("the original smart proof should verify");

    let frontier_have = click_source.find("have owner->value == 1 by simp").unwrap();
    let have_position = expansion::position_at_offset(click_source, frontier_have);
    let have_expanded = expand_c0_tactic_source_at(
        click_source,
        &sources,
        have_position.line,
        have_position.column,
    )
    .expect("the mixed-snapshot frontier-local fact should expand");
    assert!(!have_expanded.contains("have owner->value == 1 by simp"));
    assert!(
        have_expanded.contains("at(statement("),
        "the explicit certificate should retain a source statement anchor"
    );
    verify_c0_sources(&have_expanded, &sources)
        .expect("the mixed-snapshot frontier-local expansion should replay");

    let selected = click_source.find("execute_until").unwrap();
    let position = expansion::position_at_offset(click_source, selected);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("mixed-snapshot smart execution should expand");
    assert!(!expanded.contains("execute_until(statement(3));"));
    verify_c0_sources(&expanded, &sources)
        .expect("the mixed-snapshot smart execution expansion should replay");
}

#[test]
fn execute_until_expands_vector_storage_call_postconditions() {
    let init_c = r#"
struct buffer {
    int32 len;
    int32 cap;
    int32* data;
};

int32 buffer_init(struct buffer* owner, int32 data[], int32 capacity) {
    owner->len = 0;
    owner->cap = capacity;
    owner->data = data;
    return owner->len;
}
"#;
    let push_c = r#"
struct buffer {
    int32 len;
    int32 cap;
    int32* data;
};

int32 buffer_push(struct buffer* owner, int32 value) {
    int32 index;
    int32* data;
    index = owner->len;
    data = owner->data;
    data[index] = value;
    owner->len = index + 1;
    return owner->len;
}
"#;
    let pipeline_c = r#"
struct buffer {
    int32 len;
    int32 cap;
    int32* data;
};

int32 buffer_pipeline(
    struct buffer* owner,
    int32 data[],
    int32 capacity,
    int32 value
) {
    int32 result;
    result = buffer_init(owner, data, capacity);
    result = buffer_push(owner, value);
    return result;
}
"#;
    let click_source = r#"
resource empty_buffer(owner: struct buffer*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact owner->len == 0;
    fact 1 <= owner->cap;
    fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
}

resource buffer_storage(owner: struct buffer*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact loadable(owner->data[0..owner->len]);
    fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
}

resource nonempty_buffer(owner: struct buffer*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 1 <= owner->len;
    fact owner->len <= owner->cap;
    fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
}

verifying "buffer_init.c";
verifying "buffer_push.c";
verifying "buffer_pipeline.c";

int32 buffer_init(struct buffer* owner, int32 data[], int32 capacity) {
    requires 1 <= capacity;
    consumes object(owner);
    consumes data[0..capacity];
    mutable owner->len, owner->cap, owner->data;
    produces empty_buffer(owner);
    ensures result == 0;
    ensures owner->len == 0;
    ensures owner->cap == capacity;
    ensures owner->data == data;
} by {
    execute();
    fold(empty_buffer(owner));
    frame();
    simp();
}

int32 buffer_push(struct buffer* owner, int32 value) {
    requires owner->len < owner->cap;
    owns buffer_storage(owner);
    mutable owner->len, owner->data[owner->len..owner->len + 1];
    ensures result == old(owner->len) + 1;
    ensures owner->len == old(owner->len) + 1;
    ensures owner->data[old(owner->len)] == value;
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
} by {
    unfold(buffer_storage(owner));
    execute();
    fold(buffer_storage(owner));
    frame();
    simp();
}

int32 buffer_pipeline(
    struct buffer* owner,
    int32 data[],
    int32 capacity,
    int32 value
) {
    requires 1 <= capacity;
    consumes object(owner);
    consumes data[0..capacity];
    produces nonempty_buffer(owner) by {
        execute_until(statement(2));
        unfold(empty_buffer(owner));
        have 0 <= owner->len by simp;
        have owner->len <= owner->cap by simp;
        have loadable(owner->data[0..owner->len]) by simp;
        fold(buffer_storage(owner));
        execute_until(statement(3));
        unfold(buffer_storage(owner));
        have owner->len == 1 by simp;
        have 1 <= owner->len by simp;
        fold(nonempty_buffer(owner));
        step() using {};
    }
}
"#;
    let sources = [
        ("buffer_init.c", init_c),
        ("buffer_push.c", push_c),
        ("buffer_pipeline.c", pipeline_c),
    ];

    verify_c0_sources(click_source, &sources)
        .expect("the original vector-shaped proof should verify");

    let selected = click_source.rfind("execute_until").unwrap();
    let position = expansion::position_at_offset(click_source, selected);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("vector-shaped mixed-snapshot smart execution should expand");
    assert!(!expanded.contains("execute_until(statement(3));"));
    verify_c0_sources(&expanded, &sources)
        .expect("the vector-shaped mixed-snapshot expansion should replay");
}

#[test]
fn tactic_expansion_includes_a_call_at_the_execute_until_endpoint() {
    let callee_c = r#"
int32 callee(int32 x) {
    return x;
}
"#;
    let caller_c = r#"
int32 caller(int32 x) {
    int32 result;
    result = callee(x);
    return result;
}
"#;
    let click_source = r#"
verifying "callee.c";
verifying "caller.c";

int32 callee(int32 x) {
    ensures result == x;
} by {
    execute();
    simp();
}

int32 caller(int32 x) {
    ensures result == x;
} by {
    execute_until(statement(1));
    execute();
    simp();
}
"#;
    let sources = [("callee.c", callee_c), ("caller.c", caller_c)];
    let selected = click_source.find("execute_until").unwrap();
    let position = expansion::position_at_offset(click_source, selected);

    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("the endpoint call dependency should be verified before expansion");
    assert!(!expanded.contains("execute_until(statement(1));"));
}

#[test]
fn verification_session_reuses_certified_dependencies_and_rechecks_target() {
    let callee_c = r#"
int32 callee(int32 x) {
    return x;
}
"#;
    let caller_c = r#"
int32 caller(int32 x) {
    int32 result;
    result = callee(x);
    return result;
}
"#;
    let click_source = r#"
verifying "callee.c";
verifying "caller.c";

int32 callee(int32 x) {
    ensures result == x;
} by {
    execute();
    simp();
}

int32 caller(int32 x) {
    ensures result == x;
} by {
    execute();
    simp();
}
"#;
    let sources = [("callee.c", callee_c), ("caller.c", caller_c)];
    let (session, _) =
        C0VerificationSession::new(click_source, &sources).expect("baseline should verify");
    let caller_simp = click_source.rfind("simp();").unwrap();
    let position = expansion::position_at_offset(click_source, caller_simp);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("caller simp should expand");
    let expanded_position =
        c0_tactic_source_position(&expanded, &sources, "caller.contract", 0).unwrap();

    let verified = session
        .verify_at(&expanded, expanded_position.line, expanded_position.column)
        .expect("session should verify the rewritten caller");
    assert!(
        verified
            .iter()
            .all(|theorem| theorem.function_block.signature().name() == "caller")
    );

    let broken_target = expanded.replacen("assumption();", "left();", 1);
    session
        .verify_at(
            &broken_target,
            expanded_position.line,
            expanded_position.column,
        )
        .expect_err("the selected function must be rechecked");

    let changed_dependency = expanded.replacen(
        "int32 callee(int32 x) {\n    ensures result == x;",
        "int32 callee(int32 x) {\n    ensures result == x + 1;",
        1,
    );
    let error = session
        .verify_at(
            &changed_dependency,
            expanded_position.line,
            expanded_position.column,
        )
        .expect_err("dependency source changes must invalidate the baseline session");
    assert!(
        error.message().contains("outside the selected proof unit"),
        "{}",
        error.message()
    );

    let shifted = expanded.replacen("int32 caller", "\n\nint32 caller", 1);
    let shifted_position =
        c0_tactic_source_position(&shifted, &sources, "caller.contract", 0).unwrap();
    assert_ne!(shifted_position.line, position.line);
    session
        .verify_at(&shifted, shifted_position.line, shifted_position.column)
        .expect("session selection should follow the rewritten claim, not baseline coordinates");
}

#[test]
fn verification_session_keeps_partial_and_termination_rules_separate() {
    let good_c = r#"int32 countdown(int32 n) {
    int32 result;
    if (n > 0) {
        result = countdown(n - 1);
        return result;
    }
    return 0;
}"#;
    let partial_c = r#"int32 stuck(int32 n) {
    int32 result;
    if (n > 0) {
        result = stuck(n);
        return result;
    }
    return 0;
}"#;
    let click_source = r#"verifying "countdown.c";
verifying "stuck.c";

int32 countdown(int32 n) {
    decreases n;
    ensures result == 0 by auto;
}

int32 stuck(int32 n) {
    ensures result == 0 by auto;
}"#;
    let sources = [("countdown.c", good_c), ("stuck.c", partial_c)];
    let (session, _) =
        C0VerificationSession::new(click_source, &sources).expect("both contracts should verify");

    assert!(session.function_termination_is_verified("countdown"));
    assert!(!session.function_termination_is_verified("stuck"));
}

/// `condition_polarity_equivalent` used to answer through
/// `canonical_order_condition(left) == canonical_order_condition(right)`.
/// Only comparisons have a canonical order form, so every pair of
/// non-comparison conditions compared equal through `None == None`, and any
/// such premise counted as available once the context held any other
/// non-comparison condition.
#[test]
fn unrelated_non_comparison_conditions_are_not_polarity_equivalent() {
    let overflow = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedAddOverflows(
            Box::new(Bitvector32Term::Variable(Variable(1))),
            Box::new(Bitvector32Term::Constant(1)),
        ),
        false,
    );
    let constant = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    let equality = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(Variable(2))),
            Box::new(Bitvector32Term::Constant(7)),
        ),
        true,
    );

    for (left, right) in [
        (&overflow, &constant),
        (&constant, &equality),
        (&overflow, &equality),
    ] {
        assert!(
            !condition_polarity_equivalent(left, right),
            "conditions without a canonical order form must not match each other:\n  {left:?}\n  {right:?}"
        );
    }

    // Each is still equivalent to itself, and the canonical order form still
    // relates the two spellings of one comparison.
    for condition in [&overflow, &constant, &equality] {
        assert!(condition_polarity_equivalent(condition, condition));
    }
    let less_than = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessThan(
            Box::new(Bitvector32Term::Variable(Variable(1))),
            Box::new(Bitvector32Term::Variable(Variable(2))),
        ),
        true,
    );
    let greater_equal = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedGreaterEqual(
            Box::new(Bitvector32Term::Variable(Variable(1))),
            Box::new(Bitvector32Term::Variable(Variable(2))),
        ),
        false,
    );
    assert!(condition_polarity_equivalent(&less_than, &greater_equal));

    let greater_equal_true = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedGreaterEqual(
            Box::new(Bitvector32Term::Variable(Variable(2))),
            Box::new(Bitvector32Term::Variable(Variable(1))),
        ),
        true,
    );
    let reversed_less_equal = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessEqual(
            Box::new(Bitvector32Term::Variable(Variable(1))),
            Box::new(Bitvector32Term::Variable(Variable(2))),
        ),
        true,
    );
    assert!(condition_polarity_equivalent(
        &greater_equal_true,
        &reversed_less_equal
    ));
}

#[test]
fn unfolding_composite_rejects_concretely_overlapping_owned_children() {
    let c_source = r#"
        int32 preserve(int32* data) {
            return 0;
        }
    "#;
    let click_source = r#"
        resource overlapping(data: int32*) {
            owns data[0..2];
            owns data[1..3];
            fact separate(memory(data[0..2]), memory(data[1..3]));
        }

        verifying "preserve.c";

        int32 preserve(int32* data) {
            owns overlapping(data);
            ensures result == 0;
        } by {
            unfold(overlapping(data));
            execute();
            simp();
        }
    "#;

    let error = verify_c0_sources(click_source, &[("preserve.c", c_source)])
        .expect_err("a composite fact must not authorize overlapping owned children");
    assert!(
        error
            .message()
            .contains("overlapping owned memory resource facts"),
        "{}",
        error.message()
    );
}

#[test]
fn unfolding_composite_accepts_propositionally_equal_arguments() {
    let c_source = r#"
        int32 preserve(int32* left, int32* right) {
            return 0;
        }
    "#;
    let click_source = r#"
        resource cell(data: int32*) {
            owns data[0..1];
        }

        verifying "preserve.c";

        int32 preserve(int32* left, int32* right) {
            requires left == right;
            owns cell(left);
            ensures result == 0;
        } by {
            unfold(cell(right));
            execute();
            fold(cell(left));
            simp();
        }
    "#;

    verify_c0_sources(click_source, &[("preserve.c", c_source)])
        .expect("unfold should retain its equality-aware resource-consumption fallback");
}

#[test]
fn incremental_selection_follows_reverse_call_dependencies_and_ignores_comments() {
    let sources = [
        ("leaf.c", "int32 leaf(int32 x) { return x; }"),
        (
            "middle.c",
            "int32 middle(int32 x) { int32 y = leaf(x); return y; }",
        ),
        (
            "top.c",
            "int32 top(int32 x) { int32 y = middle(x); return y; }",
        ),
        ("unrelated.c", "int32 unrelated(int32 x) { return x; }"),
    ];
    let baseline = r#"
verifying "leaf.c";
verifying "middle.c";
verifying "top.c";
verifying "unrelated.c";
int32 leaf(int32 x) { ensures result == x; } by simp;
int32 middle(int32 x) { ensures result == x; } by auto;
int32 top(int32 x) { ensures result == x; } by auto;
int32 unrelated(int32 x) { ensures result == x; } by auto;
"#;
    let changed = baseline.replacen("} by simp;", "} by auto;", 1);
    let selection = c0_incremental_selection(&changed, &sources, baseline, &sources).unwrap();
    assert_eq!(selection.selected_functions, ["leaf", "middle", "top"]);
    assert_eq!(selection.reused_functions, ["unrelated"]);
    assert!(!selection.full_rebuild);
    let incremental =
        verify_c0_sources_functions(&changed, &sources, selection.selected_functions.clone());
    let clean = verify_c0_sources(&changed, &sources);
    assert!(clean.is_ok(), "clean verification failed: {clean:?}");
    assert_eq!(incremental.is_ok(), clean.is_ok(), "{incremental:?}");

    let commented_sources = [
        (
            "leaf.c",
            "// formatting-only edit\nint32 leaf(int32 x) { return x; }",
        ),
        sources[1],
        sources[2],
        sources[3],
    ];
    let unchanged =
        c0_incremental_selection(baseline, &commented_sources, baseline, &sources).unwrap();
    assert!(unchanged.selected_functions.is_empty(), "{unchanged:?}");
    assert_eq!(unchanged.reused_functions.len(), 4);
}

#[test]
fn incremental_selection_rebuilds_all_functions_for_shared_logic_changes() {
    let sources = [
        ("first.c", "int32 first(int32 x) { return x; }"),
        ("second.c", "int32 second(int32 x) { return x; }"),
    ];
    let baseline = r#"
verifying "first.c";
verifying "second.c";
predicate allowed(x: int32) { x == x }
int32 first(int32 x) { ensures result == x; } by simp;
int32 second(int32 x) { ensures result == x; } by simp;
"#;
    let changed = baseline.replace("x == x", "x == 0");
    let selection = c0_incremental_selection(&changed, &sources, baseline, &sources).unwrap();
    assert!(selection.full_rebuild);
    assert_eq!(selection.selected_functions, ["first", "second"]);
    assert!(selection.reused_functions.is_empty());
}

/// The perpetual-service example used to verify or fail depending on ambient
/// machine load: `fold(service(owner))` decided its body's separation fact
/// through an open-ended kernel search whose budget truncation was reported
/// as a missing fact. The bounded matchers now decide the respelled body
/// facts deterministically, so repeated verification must stay green under
/// the deterministic work budgets this test suite runs with.
#[test]
fn perpetual_service_example_verifies_stably_across_repeated_runs() {
    let project =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/perpetual-service");
    let mut click_paths = std::fs::read_dir(&project)
        .expect("the perpetual-service example project should exist")
        .map(|entry| entry.expect("example directory entries should be readable").path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "click"))
        .collect::<Vec<_>>();
    click_paths.sort();
    assert!(
        !click_paths.is_empty(),
        "expected a .click sidecar in {}",
        project.display()
    );
    for click_path in &click_paths {
        let click_source =
            std::fs::read_to_string(click_path).expect("the example sidecar should be readable");
        let c_sources = crate::cli::read_verifying_sources(click_path, &click_source)
            .expect("the example C sources should resolve");
        let sources = crate::cli::source_refs(&c_sources);
        verify_c0_sources(&click_source, &sources).unwrap_or_else(|error| {
            panic!("`{}` failed: {}", click_path.display(), error.message())
        });
        // The flaky fold lives in `service_step`; repeat its verification to
        // pin cross-run determinism of the shared caches and interners.
        for round in 0..4 {
            verify_c0_sources_functions(&click_source, &sources, ["service_step".to_string()])
                .unwrap_or_else(|error| {
                    panic!(
                        "repeat round {round}: `{}` failed: {}",
                        click_path.display(),
                        error.message()
                    )
                });
        }
    }
}

/// Whatever a reduced budget truncates inside `service_step`, the failure
/// must present itself as budget exhaustion. The perpetual-service fold used
/// to let a truncated kernel derivation surface as "missing pure fact" while
/// the available-fact list printed the very fact it claimed was missing.
#[test]
fn truncated_service_step_reports_the_budget_not_a_missing_fact() {
    let project =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/perpetual-service");
    let click_path = project.join("perpetual_service.click");
    let click_source =
        std::fs::read_to_string(&click_path).expect("the example sidecar should be readable");
    let c_sources = crate::cli::read_verifying_sources(&click_path, &click_source)
        .expect("the example C sources should resolve");
    let sources = crate::cli::source_refs(&c_sources);
    for simple_budget in [10_000, 40_000, 80_000, 160_000, 320_000] {
        let limits = crate::instrumentation::TacticWorkLimits {
            simple: simple_budget,
            ..Default::default()
        };
        let result = crate::instrumentation::with_tactic_work_limits(limits, || {
            verify_c0_sources_functions(&click_source, &sources, ["service_step".to_string()])
        });
        let Err(error) = result else {
            continue;
        };
        let message = error.message();
        assert!(
            message.contains("budget"),
            "a truncated run must report its budget, not a semantic failure \
             (simple budget {simple_budget}): {message}"
        );
    }
}
