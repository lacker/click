//! End-to-end step scaling: one C function per shape and size, checked with
//! one explicit simple tactic per statement, so each step's deterministic
//! work can be compared across sizes. A simple step must cost work bounded by
//! its own statement and the state it changes, not by the function's size
//! (`docs/internals/verification-efficiency.md`, and "Scaling tests" in
//! `docs/internals/testing.md`). These are the shapes of
//! `scripts/step-scaling-hunt.py` at gate sizes, with an extern callee and no
//! closing proof to keep them fast; the script runs the full versions at
//! larger sizes for investigation.

use super::*;

#[test]
fn partial_borrow_refold_ignores_unselected_siblings() {
    let (proof, sources) =
        super::expansion_tests::mdtest_sources("mdtests/refold_one_piece_of_a_borrow.md");
    let mut samples = Vec::new();
    for count in [2, 4, 8, 16] {
        let siblings = (1..count)
            .map(|start| format!("views p[{start}..{}];\n", start + 1))
            .collect::<String>();
        let proof = proof
            .replace("views p[1..2];", &siblings)
            .replace("p[0..2]", &format!("p[0..{count}]"))
            .replace(
                "extern void drop_first",
                &format!(
                    "resource rest(p: int32*) {{ {siblings} }}\n\
                     extern void drop_rest(int32* p) {{ consumes rest(p); }}\n\
                     extern void drop_first"
                ),
            )
            .replace("release_view(p[1..2]);", "fold(rest(p));\n    step();");
        let c = sources[0]
            .1
            .replace("void update", "void drop_rest(int *p);\n\nvoid update")
            .replace("    p[1] = 9;", "    drop_rest(p);\n    p[1] = 9;");
        let (result, tactics) = crate::instrumentation::collect_tactic_work(|| {
            verify_c_sources(&proof, &[(sources[0].0.as_str(), &c)])
        });
        result.unwrap_or_else(|error| panic!("at {count} pieces: {}", error.report()));
        let fold = tactics
            .iter()
            .find(|sample| sample.tactic.tactic_name == "fold")
            .expect("the first fold is measured");
        samples.push((count, fold.work));
    }
    assert!(
        samples.iter().all(|(_, work)| *work <= samples[0].1 + 32),
        "refolding one piece should not visit its siblings: {samples:?}"
    );
}

#[test]
fn branch_interface_reuses_saved_states_beside_growing_locals_and_marks() {
    let target = ProgramPointRef {
        region: CodeRegionRef::Region(2),
        kind: ProgramPointKind::Entry,
    };
    let incidental = ProgramPointRef {
        region: CodeRegionRef::Region(1),
        kind: ProgramPointKind::Exit,
    };
    let mark = ProgramPointSelector::Mark("here".into());
    let private_mark = ProgramPointSelector::Mark("only_in_one_arm".into());

    for count in [16, 64, 256] {
        let state = (0..count).fold(ExecutionState::new(), |state, index| {
            state.with_local(format!("stable_{index}"), crate::kernel::int32(index))
        });
        let mut root = RecordedStates::new();
        root.insert(incidental.clone(), state.clone());
        root.insert(mark.clone(), state.clone());
        let mut results = RecordedCallResults::default();
        results.insert(1, RetainedProgramValue::from(crate::kernel::int32(42)));
        root.set_call_result_snapshot(&mark, Some(results));
        for index in 0..count {
            root.insert(
                ProgramPointSelector::Mark(format!("mark_{index}")),
                state.clone(),
            );
        }
        let successor = state
            .clone()
            .with_local("join_value", crate::kernel::int32(7));
        let mut arm = root.clone();
        arm.insert(target.clone(), state.clone());
        arm.insert(private_mark.clone(), state.clone());
        let common = arm.common_descendant(&root, &root).expect("common prefix");

        let (records, work) = crate::instrumentation::measure_deterministic_work(|| {
            arm.for_branch_interface(&common, &target, &successor)
        });
        assert_eq!(
            work, 0,
            "scope construction indexed a value at size {count}"
        );
        assert!(std::ptr::eq(
            records.get(&mark).unwrap(),
            common.get(&mark).unwrap()
        ));
        assert_eq!(records.get(&target), Some(&successor));
        assert!(records.get(&incidental).is_none());
        assert!(records.get(&private_mark).is_none());
        assert_eq!(
            records
                .call_results_at(&mark)
                .unwrap()
                .get(&1)
                .unwrap()
                .native_compat(),
            &crate::kernel::int32(42)
        );
    }
}

#[test]
fn recorded_state_join_visits_only_changed_loop_counts() {
    use crate::kernel::{IntegerTerm, Variable};
    use crate::persistent::measure_persistent_work;

    let mut samples = Vec::new();
    for count in [16, 64, 256] {
        let original = |index: usize| Variable(8_300_000 + index as u64);
        let agreed = Variable(8_310_000);
        let left_only = Variable(8_310_001);
        let right_only = Variable(8_310_002);
        let new_common = Variable(8_310_003);

        let mut parent = RecordedStates::new();
        for index in 0..count {
            parent.record_loop_iterations(index, &IntegerTerm::Variable(original(index)));
        }
        let unchanged = parent.common_descendant(&parent, &parent).unwrap();
        assert!(
            unchanged
                .loop_iterations
                .shares_root_with(&parent.loop_iterations)
        );
        assert!(
            unchanged
                .loop_iteration_variables
                .shares_root_with(&parent.loop_iteration_variables)
        );

        let mut left = parent.clone();
        let mut right = parent.clone();
        for arm in [&mut left, &mut right] {
            arm.record_loop_iterations(0, &IntegerTerm::Variable(agreed));
            arm.record_loop_iterations(count, &IntegerTerm::Variable(new_common));
        }
        left.record_loop_iterations(1, &IntegerTerm::Variable(left_only));
        right.record_loop_iterations(1, &IntegerTerm::Variable(right_only));
        left.record_loop_iterations(count + 1, &IntegerTerm::Variable(Variable(8_310_004)));

        let (joined, work) =
            measure_persistent_work(|| left.common_descendant(&right, &parent).unwrap());
        assert_eq!(joined.loop_naming_iterations(agreed), Some(0));
        assert_eq!(joined.loop_naming_iterations(original(0)), None);
        assert_eq!(joined.loop_naming_iterations(original(1)), Some(1));
        assert_eq!(
            joined.loop_naming_iterations(original(count - 1)),
            Some(count - 1)
        );
        assert_eq!(joined.loop_naming_iterations(new_common), Some(count));
        assert_eq!(joined.loop_naming_iterations(left_only), None);
        assert_eq!(joined.loop_naming_iterations(right_only), None);
        assert!(!joined.loop_iterations.contains_key(&(count + 1)));
        assert_eq!(parent.loop_naming_iterations(original(0)), Some(0));
        samples.push((count, work));
    }
    let (small_count, small_work) = samples[0];
    for &(count, work) in &samples {
        // The same changed keys can take logarithmically longer to look up.
        let extra_levels = (count.ilog2() - small_count.ilog2()) as usize;
        assert!(
            work <= small_work + 24 * extra_levels,
            "a fixed loop-count delta should only visit changed map paths: {samples:?}"
        );
    }
}

const TOUCH_C: &str = "";
// An extern contract: the call takes the same contract-application path as a
// verified callee's, without spending the test's time verifying its body.
const TOUCH_CLICK: &str = "extern void touch(int32* data) {
    owns data[0..4];
}";

fn lines(count: usize, line: impl Fn(usize) -> String) -> String {
    (0..count).map(line).collect::<Vec<_>>().join("\n")
}

fn steps(count: usize) -> String {
    lines(count, |_| "    step();".to_string())
}

fn many_calls(n: usize) -> (String, String) {
    let calls = lines(n, |_| "    touch(data);".into());
    let c = format!(
        "struct box {{
    int32 v;
}};

{TOUCH_C}

int32 caller(int32* data, struct box* b) {{
    b->v = 5;
{calls}
    return b->v;
}}"
    );
    let steps = steps(n + 2);
    let click = format!(
        "verifying \"hunt.c\";

{TOUCH_CLICK}

int32 caller(int32* data, struct box* b) {{
    owns data[0..4];
    owns *b;
}} by {{
{steps}
}}"
    );
    (c, click)
}

fn many_objects_with_calls(n: usize, calls: usize) -> (String, String) {
    let params = (0..n)
        .map(|i| format!("struct box* b{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let sets = lines(n, |i| format!("    b{i}->v = {i};"));
    let body_calls = lines(calls, |_| "    touch(data);".into());
    let reads = (0..n)
        .map(|i| format!("b{i}->v"))
        .collect::<Vec<_>>()
        .join(" + ");
    let c = format!(
        "struct box {{
    int32 v;
}};

{TOUCH_C}

int32 caller(int32* data, {params}) {{
    int32 total;
{sets}
{body_calls}
    total = {reads};
    return total;
}}"
    );
    let owns = lines(n, |i| format!("    owns *b{i};"));
    let steps = steps(1 + n + calls + 2);
    let click = format!(
        "verifying \"hunt.c\";

{TOUCH_CLICK}

int32 caller(int32* data, {params}) {{
    owns data[0..4];
{owns}
}} by {{
{steps}
}}"
    );
    (c, click)
}

fn many_objects(n: usize) -> (String, String) {
    many_objects_with_calls(n, 1)
}

fn partial_borrow_beside_objects(n: usize) -> (String, String) {
    let (c, click) = many_objects(n);
    (
        c.replace("touch(data);", "touch_half(data);"),
        click.replace(
            TOUCH_CLICK,
            "extern void touch_half(int32* data) { owns data[0..2]; }",
        ),
    )
}

fn objects_and_calls(n: usize) -> (String, String) {
    many_objects_with_calls(n, n)
}

fn aliases(n: usize) -> (String, String) {
    let params = (0..n)
        .map(|i| format!("struct box* q{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let reads = (0..n)
        .map(|i| format!("q{i}->v"))
        .collect::<Vec<_>>()
        .join(" + ");
    let c = format!(
        "struct box {{
    int32 v;
}};

{TOUCH_C}

int32 caller(int32* data, struct box* b, {params}) {{
    int32 total;
    b->v = 1;
    touch(data);
    total = {reads};
    return total;
}}"
    );
    let requires = lines(n, |i| format!("    requires q{i} == b;"));
    let steps = steps(5);
    let click = format!(
        "verifying \"hunt.c\";

{TOUCH_CLICK}

int32 caller(int32* data, struct box* b, {params}) {{
    owns data[0..4];
    owns *b;
{requires}
}} by {{
{steps}
}}"
    );
    (c, click)
}

fn order_chain(n: usize) -> (String, String) {
    let params = (0..=n)
        .map(|i| format!("int32 x{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let stores = lines(n, |i| format!("    data[x{}] = {};", i + 1, i + 1));
    let c = format!(
        "int32 caller(int32* data, int32 len, {params}) {{
    int32 first;
    data[x0] = 100;
{stores}
    first = data[x0];
    return first;
}}"
    );
    let requires = lines(n, |i| format!("    requires x{i} < x{};", i + 1));
    let steps = steps(1 + 1 + n + 2);
    let click = format!(
        "verifying \"hunt.c\";

int32 caller(int32* data, int32 len, {params}) {{
    owns data[0..len];
    requires 0 <= x0;
{requires}
    requires x{n} < len;
}} by {{
{steps}
}}"
    );
    (c, click)
}

fn deep_chain(n: usize) -> (String, String) {
    let params = (0..=n)
        .map(|i| format!("struct node* n{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let links = lines(n, |i| format!("    n{i}->next = n{};", i + 1));
    let path = format!("n0{}", "->next".repeat(n));
    let c = format!(
        "struct node {{
    struct node* next;
    int32 v;
}};

{TOUCH_C}

int32 caller(int32* data, {params}) {{
    int32 out;
{links}
    n{n}->v = 9;
    touch(data);
    out = {path}->v;
    return out;
}}"
    );
    let owns = lines(n + 1, |i| format!("    owns *n{i};"));
    let steps = steps(1 + n + 1 + 1 + 2);
    let click = format!(
        "verifying \"hunt.c\";

{TOUCH_CLICK}

int32 caller(int32* data, {params}) {{
    owns data[0..4];
{owns}
}} by {{
{steps}
}}"
    );
    (c, click)
}

fn branches(n: usize) -> (String, String) {
    let ifs = lines(n, |i| {
        format!(
            "    if (a{i} > 0) {{
        s = s + 1;
    }}"
        )
    });
    let params = (0..n)
        .map(|i| format!("int32 a{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let c = format!(
        "int32 caller({params}) {{
    int32 s;
    s = 0;
{ifs}
    return s;
}}"
    );
    let arms = lines(n, |i| {
        let bound = i + 1;
        format!(
            "        branch ensuring {{
            fact 0 <= s;
            fact s <= {bound};
        }} {{ true => {{
            step();
            have 0 <= s by {{ close(); }}
            have s <= {bound} by {{ close(); }}
        }} false => {{
            have s <= {bound} by {{ close(); }}
        }} }}"
        )
    });
    let click = format!(
        "verifying \"hunt.c\";

int32 caller({params}) {{
    ensures result >= 0 by {{
        step();
        step();
{arms}
        step();
        close();
    }}
}}"
    );
    (c, click)
}

fn straight_line(n: usize) -> (String, String) {
    let decls = lines(n, |i| format!("    int32 x{};", i + 1));
    let assigns = lines(n, |i| format!("    x{} = x{i} + 1;", i + 1));
    let c = format!(
        "int32 caller(int32 x0) {{
{decls}
{assigns}
    return x{n};
}}"
    );
    let steps = steps(2 * n + 1);
    let click = format!(
        "verifying \"hunt.c\";

int32 caller(int32 x0) {{
    requires 0 <= x0;
    requires x0 <= 1000000;
    ensures true;
}} by {{
{steps}
}}"
    );
    (c, click)
}

fn loops(n: usize) -> (String, String) {
    let body = lines(n, |k| {
        format!(
            "    i = 0;
    while (i < 4) {{
        p[i] = {k};
        i = i + 1;
    }}"
        )
    });
    let c = format!(
        "int32 caller(int32* p) {{
    int32 i;
{body}
    return 0;
}}"
    );
    let proof = lines(n, |_| {
        "    step();
    loop { decreases 4 - i; invariant i >= 0; invariant i <= 4; }"
            .into()
    });
    let click = format!(
        "verifying \"hunt.c\";

int32 caller(int32* p) {{
    owns p[0..4];
    ensures result == 0;
}} by {{
    step();
{proof}
    step();
    close();
}}"
    );
    (c, click)
}

fn const_array(n: usize) -> (String, String) {
    let stores = lines(n, |i| format!("    data[{i}] = {i};"));
    let c = format!(
        "int32 caller(int32* data) {{
    int32 first;
{stores}
    first = data[0];
    return first;
}}"
    );
    let steps = steps(n + 3);
    let click = format!(
        "verifying \"hunt.c\";

int32 caller(int32* data) {{
    owns data[0..{n}];
}} by {{
{steps}
}}"
    );
    (c, click)
}

/// Stores into one object, each followed by a read of a cell no store
/// wrote: the read's version is the object's entry, behind every earlier
/// store into the same object. A walk back over the object's history to
/// name it costs the stores before it (`legacy_walk_naming_of_fresh_cells_still_grows_with_same_block_stores`
/// in the resource tracker's scaling tests); an indexed version does not.
fn fresh_reads_after_stores(
    n: usize,
    declarations: &str,
    parameters: &str,
    prelude: &str,
    place: impl Fn(usize) -> String,
    owns: &str,
) -> (String, String) {
    let body = lines(n, |i| {
        format!("    {} = {i};\n    seen = {};", place(i), place(n + i))
    });
    let c = format!(
        "{declarations}int32 caller({parameters}) {{
    int32 seen;
{prelude}{body}
    return seen;
}}"
    );
    let prelude_steps = prelude.lines().count();
    let steps = steps(2 * n + 2 + prelude_steps);
    let click = format!(
        "verifying \"hunt.c\";

int32 caller({parameters}) {{
{owns}
}} by {{
{steps}
}}"
    );
    (c, click)
}

fn struct_field_declarations(n: usize) -> String {
    let fields = lines(2 * n, |i| format!("    int32 f{i};"));
    format!("struct wide {{\n{fields}\n}};\n\n")
}

fn fresh_struct_fields(n: usize) -> (String, String) {
    fresh_reads_after_stores(
        n,
        &struct_field_declarations(n),
        "struct wide* w",
        "",
        |i| format!("w->f{i}"),
        "    owns *w;",
    )
}

fn fresh_array_elements(n: usize) -> (String, String) {
    fresh_reads_after_stores(
        n,
        "",
        "int32* data",
        "",
        |i| format!("data[{i}]"),
        &format!("    owns data[0..{}];", 2 * n),
    )
}

fn fresh_fields_through_a_loaded_pointer(n: usize) -> (String, String) {
    let declarations = format!(
        "{}struct holder {{\n    struct wide* inner;\n}};\n\n",
        struct_field_declarations(n)
    );
    fresh_reads_after_stores(
        n,
        &declarations,
        "struct holder* h",
        "",
        |i| format!("h->inner->f{i}"),
        "    owns *h;\n    owns *(h->inner);",
    )
}

fn many_callees(n: usize) -> (String, String) {
    let callees_c = (0..n)
        .map(|i| {
            format!(
                "void touch{i}(int32* data) {{
    return;
}}"
            )
        })
        .collect::<Vec<_>>()
        .join("\n\n");
    let calls = lines(n, |i| format!("    touch{i}(data);"));
    let c = format!(
        "struct box {{
    int32 v;
}};

{callees_c}

int32 caller(int32* data, struct box* b) {{
    b->v = 5;
{calls}
    return b->v;
}}"
    );
    let callees_click = (0..n)
        .map(|i| {
            format!(
                "void touch{i}(int32* data) {{
    owns data[0..4];
}}"
            )
        })
        .collect::<Vec<_>>()
        .join("\n\n");
    let steps = steps(n + 2);
    let click = format!(
        "verifying \"hunt.c\";

{callees_click}

int32 caller(int32* data, struct box* b) {{
    owns data[0..4];
    owns *b;
}} by {{
{steps}
}}"
    );
    (c, click)
}

fn unrelated_facts(n: usize) -> (String, String) {
    let params = (0..n)
        .map(|i| format!("int32 a{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let requires = lines(n, |i| format!("    requires a{i} < {};", i + 1000));
    let c = format!(
        "struct box {{
    int32 v;
}};

{TOUCH_C}

int32 caller(int32* data, struct box* b, {params}) {{
    b->v = 5;
    touch(data);
    return b->v;
}}"
    );
    let click = format!(
        "verifying \"hunt.c\";

{TOUCH_CLICK}

int32 caller(int32* data, struct box* b, {params}) {{
    owns data[0..4];
    owns *b;
{requires}
}} by {{
    step();
    step();
    step();
}}"
    );
    (c, click)
}

fn heap_objects(n: usize) -> (String, String) {
    let decls = lines(n, |i| format!("    struct box* p{i};"));
    let makes = lines(n, |i| format!("    p{i} = make_box();\n    p{i}->v = {i};"));
    let drops = lines(n, |i| format!("    drop_box(p{i});"));
    let c = format!(
        "struct box {{
    int32 v;
}};

int32 caller() {{
{decls}
{makes}
{drops}
    return 0;
}}"
    );
    let make_proof = lines(n, |i| {
        format!(
            "    step();
    step();
    unfold(boxed(p{i}));
    step();
    fold(boxed(p{i}));"
        )
    });
    let steps = steps(n);
    let click = format!(
        "verifying \"hunt.c\";

resource boxed(p: struct box*) {{
    owns *p;
}}

extern struct box* make_box() {{
    produces boxed(result);
}}

extern void drop_box(struct box* p) {{
    consumes boxed(p);
}}

int32 caller() {{
    ensures true;
}} by {{
{steps}
{make_proof}
{steps}
    step();
}}"
    );
    (c, click)
}

/// One verified size of a shape: each `step()`'s work in proof order beside
/// the statement it executes with digits blanked, so that steps doing the
/// same thing at different positions share a role, each `loop` clause's
/// work, and each other simple resource tactic's work in proof order by
/// tactic. The steps execute `caller`'s statements in source order, one each.
struct Run {
    statements: usize,
    steps: Vec<(String, usize)>,
    loops: Vec<usize>,
    resource_tactics: Vec<(&'static str, Vec<usize>)>,
}

impl Run {
    /// The steps, each beside the statement it executes; refuses a run whose
    /// steps do not pair one to one with `caller`'s statements.
    fn statement_steps(&self, name: &str) -> &[(String, usize)] {
        assert_eq!(
            self.steps.len(),
            self.statements,
            "{name}: expected one step per statement"
        );
        &self.steps
    }
}

/// The simple tactics besides `step` a shape's proof repeats per object:
/// each must cost the same at every position, as a step must.
const RESOURCE_TACTICS: [&str; 2] = ["unfold", "fold"];

fn run(shape: impl FnOnce(usize) -> (String, String), n: usize) -> Run {
    let (c, click) = shape(n);
    let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
        verify_c_sources(&click, &[("hunt.c", c.as_str())])
    });
    result.unwrap_or_else(|error| panic!("size {n}: {}", error.message()));
    let body = c
        .split("caller(")
        .nth(1)
        .expect("the shape defines `caller`");
    let roles = body
        .lines()
        .skip(1)
        .map(str::trim)
        .filter(|line| line.ends_with(';'))
        .map(|line| {
            // Each number becomes one `#`, so `x9` and `x10` share a role.
            let mut role = String::new();
            for ch in line.chars() {
                if !ch.is_ascii_digit() {
                    role.push(ch);
                } else if !role.ends_with('#') {
                    role.push('#');
                }
            }
            role
        })
        .flat_map(|role| {
            // The heap-object fixture's factory expression is two checked
            // operations. Compare calls with calls and assignments with
            // assignments, rather than mixing their work in one role.
            if role.ends_with(" = make_box();") {
                vec![format!("call {role}"), format!("assign {role}")]
            } else {
                vec![role]
            }
        })
        .collect::<Vec<_>>();
    let in_order = |name: &str| {
        // A `loop` clause also reports its own nested bookkeeping at the same
        // index; the clause is the larger.
        let mut work = BTreeMap::<usize, usize>::new();
        for sample in samples.iter().filter(|sample| {
            sample.tactic.claim.contains("caller") && sample.tactic.tactic_name == name
        }) {
            let entry = work.entry(sample.tactic.tactic_index).or_default();
            *entry = (*entry).max(sample.work);
        }
        work.into_values().collect::<Vec<_>>()
    };
    Run {
        statements: roles.len(),
        steps: in_order("step")
            .into_iter()
            .enumerate()
            .map(|(index, work)| (roles.get(index).cloned().unwrap_or_default(), work))
            .collect(),
        loops: in_order("loop"),
        resource_tactics: RESOURCE_TACTICS
            .into_iter()
            .map(|name| (name, in_order(name)))
            .collect(),
    }
}

/// Work differences this small are not drift: a logarithmic index lookup
/// changes by at most a unit or two between adjacent positions, and a
/// one-off change in spelling does not repeat. A cost linear in earlier
/// statements, even four units per position on a step of 150, exceeds it.
fn band(work: usize) -> usize {
    2 + work / 256
}

#[test]
fn repeated_stores_ignore_numeric_address_aliases_without_cached_cells() {
    #[derive(Clone, Copy, PartialEq)]
    enum OtherEquality {
        ExactPointer,
        RawWord,
    }
    let measure = |size, alias_base, frame_owners, extra_requirement| {
        let run = run(
            |size| {
                let mut parameters = "int32* p, int32* other".to_string();
                // Each initialized ownership clause seeds a cached cell.
                let mut frame = String::new();
                for i in 0..frame_owners {
                    parameters += &format!(", int32* frame{i}");
                    frame += &format!("    owns *frame{i};\n");
                }
                let (globals, mut requirements) = match extra_requirement {
                    Some(OtherEquality::RawWord) => {
                        parameters += ", uint64 u, uint64 v";
                        ("", "    requires u == v;\n".to_string())
                    }
                    Some(OtherEquality::ExactPointer) => (
                        "int32 sentinel;\n",
                        "    requires other == &sentinel;\n".to_string(),
                    ),
                    None => ("", String::new()),
                };
                for i in 0..size {
                    parameters += &format!(", int32* alias{i}");
                    requirements += &format!(
                        "    requires ({alias_base} as uint64) == (alias{i} as uint64);\n"
                    );
                }
                let c = format!(
                    "{globals}void caller({parameters}) {{\n    *p = 17;\n    *p = 18;\n    *p = 19;\n    return;\n}}"
                );
                let click = format!(
                    "verifying \"hunt.c\";\nvoid caller({parameters}) {{\n    owns *p;\n{frame}{requirements}}} by {{ step(); step(); step(); step(); }}"
                );
                (c, click)
            },
            size,
        );
        let steps = run.statement_steps("repeated numeric-address stores");
        [steps[1].1, steps[2].1]
    };
    // A 16-alias star already distinguishes the old scan from the indexed
    // check. Keep the larger source probes out of the budgeted gate.
    for (frame_owners, extra_requirement) in [
        (0, None),
        (1, None),
        (8, None),
        (8, Some(OtherEquality::ExactPointer)),
        (8, Some(OtherEquality::RawWord)),
    ] {
        let samples = [2, 8, 16].map(|size| {
            (
                measure(size, "p", frame_owners, extra_requirement),
                measure(size, "other", frame_owners, extra_requirement),
            )
        });
        eprintln!("repeated store work with connected and disconnected aliases: {samples:?}");
        let connected_baseline = samples[0].0.into_iter().min().unwrap();
        let disconnected_baseline = samples[0].1.into_iter().min().unwrap();
        for (connected, disconnected) in samples {
            for (connected, disconnected) in connected.into_iter().zip(disconnected) {
                assert!(connected <= connected_baseline + 16, "{samples:?}");
                assert!(disconnected <= disconnected_baseline + 16, "{samples:?}");
                if extra_requirement != Some(OtherEquality::ExactPointer) {
                    assert!(connected <= disconnected + 16, "{samples:?}");
                }
            }
        }
    }
}

/// Whether work along successive positions drifts: its last changes (three,
/// or two over three positions) all move the same way by more than `band`.
/// A step whose cost depends on how many earlier statements ran changes by
/// about the same amount at every position; a warm-up (the first call, the
/// first store into a block) jumps once and then holds.
fn drifts(work: &[usize]) -> bool {
    if work.len() < 3 {
        return false;
    }
    if rises_steadily(work) {
        return true;
    }
    let tail = &work[work.len() - work.len().min(4)..];
    let changes = tail
        .windows(2)
        .map(|pair| pair[1] as i64 - pair[0] as i64)
        .collect::<Vec<_>>();
    let large = |change: i64, at: usize| change.unsigned_abs() as usize > band(at);
    changes
        .iter()
        .zip(&tail[1..])
        .all(|(change, at)| *change > 0 && large(*change, *at))
        || changes
            .iter()
            .zip(&tail[1..])
            .all(|(change, at)| *change < 0 && large(*change, *at))
}

/// Whether work rises slowly but steadily: over the last half of its
/// positions (at least five), it never falls and rises at three in four of
/// them. A cost of even one unit per earlier statement rises at every
/// position; a logarithmic index rises only where the count doubles, and a
/// warm-up holds once it has jumped. `drifts`' band cannot see the first,
/// which grows by less than the band at each step.
fn rises_steadily(work: &[usize]) -> bool {
    let tail = &work[work.len() - work.len().div_ceil(2)..];
    if tail.len() < 5 {
        return false;
    }
    let changes = tail
        .windows(2)
        .map(|pair| pair[1] as i64 - pair[0] as i64)
        .collect::<Vec<_>>();
    changes.iter().all(|change| *change >= 0)
        && changes.iter().filter(|change| **change > 0).count() * 4 >= changes.len() * 3
}

/// The roles of `run` whose steps or resource tactics drift, with their
/// work.
fn drifting_roles(name: &str, run: &Run) -> Vec<(String, Vec<usize>)> {
    let mut roles = BTreeMap::<String, Vec<usize>>::new();
    for (role, work) in run.statement_steps(name) {
        roles.entry(role.clone()).or_default().push(*work);
    }
    for (tactic, work) in &run.resource_tactics {
        roles.insert(format!("{tactic} tactic"), work.clone());
    }
    roles.into_iter().filter(|(_, work)| drifts(work)).collect()
}

/// A shape whose repeated statements must each cost the same at every
/// position, verified once at `n`.
fn assert_no_drift(name: &str, shape: fn(usize) -> (String, String), n: usize) {
    let drifting = drifting_roles(name, &run(shape, n));
    assert!(
        drifting.is_empty(),
        "{name} at {n}: a step's work drifts with the statements before it \
         (roadmap/scaling.md): {drifting:?}"
    );
}

/// The largest work of the steps executing `role` at each size, which must
/// not grow beyond `band` between the sizes: the shape grows state the step
/// does not touch.
fn assert_flat_across(
    name: &str,
    shape: fn(usize) -> (String, String),
    sizes: [usize; 2],
    role: &str,
) {
    let largest = sizes.map(|n| {
        run(shape, n)
            .statement_steps(name)
            .iter()
            .filter(|(step, _)| step == role)
            .map(|(_, work)| *work)
            .max()
            .unwrap_or_else(|| panic!("{name} at {n}: no `{role}` step"))
    });
    assert!(
        largest[1] <= largest[0] + band(largest[0]),
        "{name}: `{role}` grows from {} to {} between sizes {} and {}, with state it does \
         not touch (roadmap/scaling.md)",
        largest[0],
        largest[1],
        sizes[0],
        sizes[1]
    );
}

#[test]
fn repeated_calls_cost_the_same_at_every_position() {
    assert_no_drift("many_calls", many_calls, 12);
}

#[test]
fn calls_beside_owned_objects_cost_the_same_at_every_position() {
    assert_no_drift("objects_and_calls", objects_and_calls, 12);
}

#[test]
fn ordered_index_stores_cost_the_same_at_every_position() {
    // A store's cost climbs with the stores within about 32 positions of it
    // and then holds: a bounded window, run past so the steady-rise rule
    // sees it level.
    assert_no_drift("order_chain", order_chain, 48);
}

#[test]
fn checked_indexed_store_skips_a_separately_owned_array() {
    let work = [2, 8, 16].map(|size| {
        [false, true].map(|ordered| {
            let sample = run(
                |size| {
                    let signature = "void caller(int32* a, int32* b, int32 length, int32 i, int32 j)";
                    let (bound, order) = if ordered {
                        ("length", "    requires i < j;\n")
                    } else {
                        // An upper bound that is another variable would rank
                        // `i` even without a second order premise.
                        ("32", "")
                    };
                    let filled = lines(size, |index| format!("    a[{index}] = {index};"));
                    let c = format!("{signature} {{\n{filled}\n    b[i] = 1;\n    b[i] = 2;\n    b[i] = 3;\n    return;\n}}");
                    let proof = steps(size + 4);
                    let click = format!(
                        "verifying \"hunt.c\";\n{signature} {{\n    owns a[0..{size}];\n    owns b[0..{bound}];\n    requires 0 <= i;\n    requires i < {bound};\n{order}}} by {{\n{proof}\n}}"
                    );
                    (c, click)
                },
                size,
            );
            let stores = sample.statement_steps("indexed store beside a separate owner");
            [stores[size + 1].1, stores[size + 2].1]
        })
    });
    eprintln!("warmed indexed stores at 2/8/16 separate cells: {work:?}");
    for (baseline, largest) in work[0]
        .into_iter()
        .flatten()
        .zip(work[2].into_iter().flatten())
    {
        assert!(largest <= baseline + 32, "{work:?}");
    }
}

#[test]
fn pointer_field_links_cost_the_same_at_every_position() {
    assert_no_drift("deep_chain", deep_chain, 12);
}

#[test]
fn straight_line_assignments_cost_the_same_at_every_position() {
    assert_no_drift("straight_line", straight_line, 12);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: compares four complete source proofs"]
fn successful_steps_do_not_read_the_held_resource_list_for_diagnostics() {
    use crate::surface::proof::take_step_diagnostic_resource_reads;

    let samples = [1, 2, 4, 8].map(|n| {
        let params = (0..n)
            .map(|i| format!("int32* p{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let owns = lines(n, |i| format!("    owns *p{i};"));
        // Each repetition adds a decided branch and one scalar assignment,
        // both checked with all n unrelated resources held.
        let body = lines(n, |_| "    if (x == 0) x = 0;".into());
        let c = format!("int32 caller({params}) {{ int32 x; x = 0;\n{body}\nreturn x; }}");
        let steps = steps(3 + n * 2);
        let click = format!(
            "verifying \"hunt.c\";\nint32 caller({params}) {{\n{owns}\n}} by {{\n{steps}\n}}"
        );
        take_step_diagnostic_resource_reads();
        verify_c_sources(&click, &[("hunt.c", c.as_str())])
            .unwrap_or_else(|error| panic!("size {n}: {}", error.message()));
        take_step_diagnostic_resource_reads()
    });
    assert!(
        samples == [0; 4],
        "resource entries read for step diagnostics: {samples:?}"
    );
}

#[test]
fn constant_index_stores_cost_the_same_at_every_position() {
    assert_no_drift("const_array", const_array, 12);
}

/// The legacy-walk queries `operation` makes: their total count.
fn legacy_walk_queries(operation: impl FnOnce()) -> usize {
    crate::kernel::resource_tracker::legacy_walk_audit::capture(operation)
        .lines()
        .filter_map(|line| line.split('\t').next()?.parse::<usize>().ok())
        .sum()
}

/// Reads of cells no store wrote, each after stores into the same object,
/// cost the same at every position, and an object the program point indexes
/// name never reaches the legacy walk.
#[test]
fn fresh_reads_after_same_object_stores_cost_the_same_at_every_position() {
    for (name, shape) in [
        ("fresh_struct_fields", fresh_struct_fields as fn(usize) -> _),
        ("fresh_array_elements", fresh_array_elements),
    ] {
        let mut drifting = Vec::new();
        let queries = legacy_walk_queries(|| drifting = drifting_roles(name, &run(shape, 12)));
        assert!(
            drifting.is_empty(),
            "{name}: a step's work drifts with the statements before it: {drifting:?}"
        );
        assert_eq!(queries, 0, "{name}: a read reached the legacy walk");
    }
}

/// The same shape through a loaded pointer still reaches the legacy walk
/// (`roadmap/smart-tactics.md`, "Program-point memory migration"). Its steps
/// must not drift; once its reads have indexed versions, the second
/// assertion fails, and this test joins the one above.
#[test]
fn known_legacy_fresh_reads_through_a_loaded_pointer_cost_the_same_at_every_position() {
    let name = "fresh_fields_through_a_loaded_pointer";
    let mut drifting = Vec::new();
    let queries = legacy_walk_queries(|| {
        drifting = drifting_roles(name, &run(fresh_fields_through_a_loaded_pointer, 12));
    });
    assert!(
        drifting.is_empty(),
        "{name}: a step's work drifts with the statements before it: {drifting:?}"
    );
    assert!(
        queries > 0,
        "{name}: no read reached the legacy walk; move this shape into \
         `fresh_reads_after_same_object_stores_cost_the_same_at_every_position`"
    );
}

#[test]
fn calls_to_distinct_callees_cost_the_same_at_every_position() {
    assert_no_drift("many_callees", many_callees, 12);
}

#[test]
fn a_call_ignores_unrelated_facts() {
    assert_flat_across("unrelated_facts", unrelated_facts, [1, 3], "touch(data);");
}

#[test]
fn a_call_ignores_aliases_of_an_owned_object() {
    assert_flat_across("aliases", aliases, [1, 3], "touch(data);");
}

#[test]
fn a_call_ignores_unrelated_owned_objects() {
    assert_flat_across("many_objects", many_objects, [1, 3], "touch(data);");
}

#[test]
fn repeated_writing_calls_ignore_unrelated_folded_owners() {
    let check = |owners, calls, distinct_families| {
        let fixture = |owners| {
            let parameters = (0..owners)
                .map(|index| format!("int32* p{index}"))
                .collect::<Vec<_>>()
                .join(", ");
            let family = |index| if distinct_families { index } else { 0 };
            let definitions = lines(if distinct_families { owners } else { 1 }, |index| {
                format!("resource boxed{index}(p: int32*) {{ owns *p; }}")
            });
            let kept = lines(owners, |index| {
                format!("    owns boxed{}(p{index});", family(index))
            });
            let c = format!(
                "void caller(int32* scratch, {parameters}) {{\n{}\n}}",
                lines(calls, |_| "    ping(scratch);".into())
            );
            let click = format!(
                r#"verifying "hunt.c";
{definitions}
extern void ping(int32* scratch) {{ owns *scratch; ensures *scratch == 7; }}
void caller(int32* scratch, {parameters}) {{
    owns *scratch;
{kept}
}} by {{
{}
}}"#,
                steps(calls)
            );
            (c, click)
        };
        let result = run(fixture, owners);
        result
            .statement_steps("repeated writing calls")
            .iter()
            .map(|(_, work)| *work)
            .collect::<Vec<_>>()
    };

    let widths = [2, 4, 8, 16];
    let by_width = widths.map(|owners| check(owners, 4, false));
    for (owners, work) in widths.into_iter().zip(&by_width).skip(1) {
        // The second call catches the cell index up with the first call's
        // removals. Charge the diff and the index update once per owner.
        assert!(
            work[1] <= by_width[0][1] + 2 * (owners - widths[0]) + 8,
            "catching up the call cell index revisits folded owners: {by_width:?}"
        );
        for (baseline, widened) in by_width[0][2..].iter().zip(&work[2..]) {
            assert!(
                *widened <= baseline + 8,
                "writing calls revisit retained folded owners: {by_width:?}"
            );
        }
    }
    // Grow the call sequence at a fixed width to detect repeated upkeep.
    let longer = check(16, 12, false);
    assert!(
        longer[4..].iter().all(|work| *work <= longer[3] + 32),
        "repeated writing calls revisit earlier calls: {longer:?}"
    );
    for (owners, one_family) in widths.into_iter().zip(&by_width) {
        let distinct = check(owners, 4, true);
        assert_eq!(
            &one_family[2..],
            &distinct[2..],
            "writing calls enumerate {owners} retained resource families"
        );
    }
}

#[test]
fn inline_stores_ignore_unrelated_owned_parameter_runs() {
    let samples = [4, 8, 16, 32].map(|owners| {
        let parameters = (0..owners)
            .map(|index| format!("int32* p{index}"))
            .collect::<Vec<_>>()
            .join(", ");
        let kept = lines(owners, |index| format!("    owns *p{index};"));
        let c = format!(
            "#include \"ping.h\"\nvoid caller(int32* scratch, {parameters}) {{\n{}\n}}",
            lines(4, |index| format!("    ping(scratch, {});", 7 + index))
        );
        let header = "static inline void ping(int32* p, int32 value) { *p = value; }";
        let click = format!(
            r#"verifying "hunt.c";
void caller(int32* scratch, {parameters}) {{
    owns *scratch;
{kept}
    ensures *scratch == 10;
}} by {{
{}
}}"#,
            steps(4)
        );
        let (verified, samples) = crate::instrumentation::collect_tactic_work(|| {
            verify_c_sources(&click, &[("hunt.c", &c), ("ping.h", header)])
        });
        verified.unwrap_or_else(|error| panic!("{owners} owners: {}", error.message()));
        let calls: Vec<_> = samples
            .into_iter()
            .filter(|sample| {
                sample.tactic.claim == "caller.contract" && sample.tactic.tactic_name == "step"
            })
            .map(|sample| sample.work)
            .collect();
        assert_eq!(calls.len(), 4);
        calls[3]
    });
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 8),
        "one inline store revisits unrelated parameter runs: {samples:?}"
    );
}

#[test]
fn modular_call_reservation_ignores_unrelated_caller_state() {
    use crate::instrumentation::VerificationEvent;

    for with_owners in [false, true] {
        let samples = [4, 16, 64].map(|count| {
            let mut parameters = "int32 input".to_owned();
            let mut owns = String::new();
            let mut setup = String::new();
            for i in 0..count {
                setup += &format!("    int32 spare{i}; spare{i} = input;\n");
                if with_owners {
                    parameters += &format!(", int32* p{i}");
                    owns += &format!("    owns *p{i};\n");
                }
            }
            let c = format!(
                "void leaf(void) {{ return; }}\nvoid caller({parameters}) {{\n{setup}    leaf(); leaf(); leaf(); return;\n}}"
            );
            let proof = format!(
                "verifying \"hunt.c\";\nvoid leaf() {{ ensures true; }} by {{ step(); }}\nvoid caller({parameters}) {{\n{owns}    ensures true;\n}} by {{ {} }}",
                steps(2 * count + 4)
            );
            let (result, events) =
                crate::instrumentation::collect(|| verify_c_sources(&proof, &[("hunt.c", &c)]));
            result.unwrap_or_else(|error| panic!("size {count}: {}", error.message()));
            let calls = events
                .into_iter()
                .filter_map(|event| match event {
                    VerificationEvent::OperationFinished { name, function, work, .. }
                        if name == "verified call variable collection" && function == "leaf" =>
                    {
                        Some(work)
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(calls.len(), 3);
            assert!(calls[0] <= 5 * count + 16, "{calls:?}");
            calls
        });
        eprintln!("call reservation work at 4/16/64, owned={with_owners}: {samples:?}");
        for (small, large) in samples[0].iter().zip(&samples[2]).skip(1) {
            assert!(*large <= *small + 16, "{samples:?}");
        }
    }
}

// Splitting a caller's owner must not enumerate the other parameter owners
// that happen to share its external-argument memory block.
#[test]
fn a_partial_borrow_call_ignores_unrelated_owned_objects() {
    use crate::instrumentation::VerificationEvent as Event;
    let samples = [1_usize, 8, 64].map(|size| {
        let (run, events) =
            crate::instrumentation::collect(|| run(partial_borrow_beside_objects, size));
        let (step_index, (_, work)) = run
            .statement_steps("partial_borrow_beside_objects")
            .iter()
            .enumerate()
            .find(|(_, (role, _))| role == "touch_half(data);")
            .expect("one partial borrow call");
        let mut active = Vec::new();
        let mut footprint_work = 0;
        let mut publications = 0;
        for event in events {
            match event {
                Event::TacticStarted(tactic) => active.push(tactic),
                Event::TacticFinished { tactic, .. } | Event::TacticFailed(tactic) => {
                    if let Some(index) = active.iter().rposition(|current| current == &tactic) {
                        active.remove(index);
                    }
                }
                Event::OperationFinished { name, work, .. }
                    if name == "prepare ownership footprint"
                        && active.last().is_some_and(|tactic| {
                            tactic.claim.contains("caller")
                                && tactic.tactic_name == "step"
                                && tactic.tactic_index == step_index
                        }) =>
                {
                    footprint_work += work;
                    publications += 1;
                }
                _ => {}
            }
        }
        assert!(
            publications > 0,
            "size={size}: no ownership publication recorded"
        );
        let selected_work = work
            .checked_sub(footprint_work)
            .expect("publication work belongs to the selected step's exclusive work");
        (size, selected_work)
    });
    // Publication updates only canonical-tree paths, separately bounded by
    // the footprint scaling test. Their lengths vary with legitimate retained
    // observation identities; the rest of this selected call stays flat.
    for (size, work) in &samples[1..] {
        assert!(
            *work <= samples[0].1 + band(samples[0].1),
            "partial borrow selected work at {size}: {samples:?}"
        );
    }
}

#[test]
fn a_branch_arm_step_ignores_earlier_branches() {
    // The first branch has a literal accumulator; later ones have symbolic
    // bounds. Compare more sizes to distinguish that fixed shape change
    // from work that keeps growing with earlier branches.
    let largest = [1, 3, 7].map(|n| {
        let (c, click) = branches(n);
        let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
            verify_c_sources(&click, &[("hunt.c", c.as_str())])
        });
        result.unwrap_or_else(|error| panic!("branches at {n}: {}", error.message()));
        samples
            .iter()
            .filter(|sample| sample.tactic.tactic_name == "step")
            .map(|sample| sample.work)
            .max()
            .expect("branch steps")
    });
    eprintln!("branch step work at 1/3/7 branches: {largest:?}");
    assert!(
        !drifts(&largest) && largest[2] <= largest[1] + band(largest[1]),
        "branch step work grows: {largest:?}"
    );
}

/// A plain `unfold` normalizes around the body it opens, not the whole
/// context: the facts whole-context normalization visits grow linearly with
/// the objects a proof holds, where renormalizing at every `unfold` grew with
/// their square. Normalization is uncharged, so step work cannot see it.
#[test]
fn unfolding_one_object_does_not_renormalize_every_held_object() {
    let visited = [8, 32].map(|n| {
        crate::kernel::take_whole_normalization_facts();
        run(heap_objects, n);
        crate::kernel::take_whole_normalization_facts()
    });
    // Four times the objects: about four times the visits (here 145 to
    // 577), where renormalizing at every `unfold` visited nine (237 to 2,097).
    assert!(
        visited[1] <= visited[0] * 5,
        "whole-context normalization visited {visited:?} facts at 8 and 32 objects"
    );
}

#[test]
fn heap_object_stores_and_releases_cost_the_same_at_every_position() {
    assert_no_drift("heap_objects", heap_objects, 12);
}

/// A `loop` clause's work does not depend on the loops before it: it reads
/// the contexts and indexes the proof keeps rather than rebuilding them from
/// every earlier loop's facts. Five loops, because the first clause's own
/// warm-up hides a drift among only three.
#[test]
fn sequential_loop_clauses_cost_the_same_at_every_position() {
    let loops = run(loops, 5).loops;
    assert!(
        !drifts(&loops),
        "sequential loop clauses drift with the loops before them: {loops:?}"
    );
}

/// Later loop clauses reuse the function's parameter index and annotation
/// metadata even when the signature contains many unrelated pointers.
#[test]
fn later_loop_clauses_ignore_unreferenced_parameters() {
    let work = [4, 16, 48].map(|count| {
        let result = run(
            |count| {
                let mut parameters = "int32* p, int32 n, int32 m".to_owned();
                for i in 0..count {
                    parameters += &format!(", int32* unused{i}");
                }
                let c = format!(
                    "void caller({parameters}) {{
    while (n > 0) {{
        n = 0;
    }}
    while (m > 0) {{
        m = 0;
    }}
    *p = 7;
    return;
}}"
                );
                let click = format!(
                    "verifying \"hunt.c\";
void caller({parameters}) {{
    owns *p;
    requires n >= 0;
    requires m >= 0;
}} by {{
    loop {{ decreases n; invariant n >= 0; initialize by close(); maintain by {{ step(); }} }}
    loop {{ decreases m; invariant m >= 0; initialize by close(); maintain by {{ step(); }} }}
    step();
    step();
}}"
                );
                (c, click)
            },
            count,
        );
        assert_eq!(result.loops.len(), 2);
        result.loops[1]
    });
    assert!(
        work.iter().max().unwrap() - work.iter().min().unwrap() <= 32,
        "second loop work with 4/16/48 unrelated parameters: {work:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: checks three complete writing loops at four sizes"]
fn writing_loop_havoc_ignores_untouched_scalar_slots() {
    let costs = [4, 16, 64, 128].map(|count| {
        let run = run(
            |count| {
                let (c, proof) = loops(3);
                let locals = lines(count, |index| {
                    format!("    int32 spare{index};\n    spare{index} = {index};")
                });
                let c = c.replace("    int32 i;", &format!("    int32 i;\n{locals}"));
                let proof = proof.replacen(
                    "    step();",
                    "    step();\n".repeat(1 + 2 * count).trim_end(),
                    1,
                );
                (c, proof)
            },
            count,
        );
        // The first loop annotates the whole function. Measure a later
        // loop with the same body, write footprint and invariant shape.
        assert_eq!(run.loops.len(), 3);
        run.loops[2]
    });
    let (min, max) = (costs.iter().min().unwrap(), costs.iter().max().unwrap());
    assert!(
        max - min <= 90,
        "warmed loop work with 4/16/64/128 retained scalar slots: {costs:?}"
    );
}

/// The contexts a `loop` tactic builds, charged or not, do not grow with
/// the loops before it. Its executions copy the path's facts, and the
/// initialization proof's indexed facts are the ones the proof keeps,
/// extended by the loop's own facts. Building them from every path fact at
/// each loop (as once happened) assumes a further context entry per earlier
/// fact at every loop.
///
/// Nor does the rest of a clause's uncharged work, counted here alongside:
/// the path facts it copies out of its persistent fact list into flat
/// vectors and files in the list's exact index (`PureFactList`); the reserved-variable sets it collects for
/// fresh identities (`LazyReservedVariables`); the variables its facts
/// hand to their fact sets' reservations beyond already reserved
/// states; the whole-function annotation walks it makes
/// (`LoopAnnotation`); the structural clauses it reads out of the function
/// block's clause list (`StructuralClauses`); the statements its loop
/// lookups visit to find the loop in the C and kernel bodies; and the
/// statements putting its lowered loop in place rebuilds
/// (`KernelLoopPaths`). Each once grew
/// with the loops before: the list was a flat copy indexed afresh at every
/// loop, every rule and loop head collected the whole path context's
/// variables, every fact re-collected its states' variables, every loop
/// re-annotated the whole function, binding a clause rebuilt the block's
/// clause vector and its label, scope and region checks walked it, and each
/// lookup walked the body from its first statement, and the body's
/// right-nested pair tree put every statement before the loop on its path.
///
/// Across the twelve-loop run, the last clause also costs what the second
/// does. A drift of a unit or two per earlier loop is below the band between
/// neighbours: restoring the entry's blocks at each loop head once rebuilt
/// the block table, and comparing it walked every block declared so far.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.2s in the parallel gate"]
fn sequential_loops_build_the_same_context_entries_each() {
    let counts = || {
        let [copied, indexed] = crate::surface::pure_fact_list::fact_list_entry_counts();
        [
            (
                "context entries",
                crate::kernel::reasoning::path_facts::context_rebuild_entries(),
            ),
            ("flat fact copies", copied),
            ("fact index entries", indexed),
            (
                "reservation collections",
                crate::kernel::lazy_reservation_collections(),
            ),
            (
                "reserved fact variables",
                crate::kernel::proof::reserved_fact_variable_entries(),
            ),
            (
                "annotation walks",
                crate::surface::lowering::loop_annotation_walks(),
            ),
            (
                "structural clause visits",
                crate::surface::structural_clauses::structural_clause_visits(),
            ),
            (
                "loop lookup statements",
                crate::surface::lowering::loop_lookup_nodes(),
            ),
            (
                "loop replacement statements",
                crate::surface::lowering::kernel_loop_replacement_steps(),
            ),
        ]
    };
    let runs = [3, 6, 12].map(|n| {
        let before = counts();
        let run = run(loops, n);
        let after = counts();
        (
            std::array::from_fn::<_, 9, _>(|index| {
                (after[index].0, after[index].1 - before[index].1)
            }),
            run.loops,
        )
    });
    for index in 0..9 {
        let name = runs[0].0[index].0;
        let entries = runs.each_ref().map(|(counts, _)| counts[index].1);
        let per_loop = [(entries[1] - entries[0]) / 3, (entries[2] - entries[1]) / 6];
        assert!(
            entries[1] >= entries[0] && entries[2] >= entries[1],
            "{name}: a longer run counts fewer ({entries:?})"
        );
        assert!(
            per_loop[1] <= per_loop[0] + band(per_loop[0]),
            "each further loop counts {} {name} at 3 to 6 loops and {} at 6 to 12 ({entries:?})",
            per_loop[0],
            per_loop[1]
        );
    }
    // A loop clause's annotation lowers its own loop; only the first walks
    // the whole function.
    let annotation_walks = runs.each_ref().map(|(counts, _)| {
        counts
            .iter()
            .find(|(name, _)| *name == "annotation walks")
            .unwrap()
            .1
    });
    assert!(
        annotation_walks.iter().all(|count| *count == 1),
        "loop tactics walk the whole function more than once per claim: {annotation_walks:?}"
    );
    let clauses = &runs[2].1;
    let (second, last) = (clauses[1], clauses[clauses.len() - 1]);
    assert!(
        last <= second + band(second),
        "the last of twelve loop clauses costs {last} where the second costs {second}: \
         {clauses:?}"
    );
}

#[test]
fn drift_rules_separate_slow_drift_from_warm_up() {
    // One unit per earlier statement, too small for the band at any position.
    assert!(drifts(&(300..312).collect::<Vec<_>>()));
    // A warm-up jump, then level.
    assert!(!drifts(&[44, 300, 306, 306, 306, 306, 306, 306, 306, 306]));
    // A bounded window: climbs, then holds over the last half.
    let window = (0..48).map(|i| 300 + 2 * i.min(16)).collect::<Vec<_>>();
    assert!(!drifts(&window));
}

/// The work to verify a function that owns one object per parameter and does
/// nothing, at each of `sizes`. A first verification parses shared prelude
/// definitions later ones reuse, so a discarded one runs first.
fn owned_parameter_entry_work(sizes: [usize; 3]) -> [(usize, usize); 3] {
    let work = |n: usize| {
        let params = (0..n)
            .map(|i| format!("struct box* b{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let owns = lines(n, |i| format!("    owns *b{i};"));
        let c = format!(
            "struct box {{
    int32 v;
}};

void caller({params}) {{
    return;
}}"
        );
        let click = format!(
            "verifying \"hunt.c\";

void caller({params}) {{
{owns}
}} by {{
    step();
}}"
        );
        let ((result, work), events) = crate::instrumentation::collect(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                verify_c_sources(&click, &[("hunt.c", c.as_str())])
            })
        });
        result.unwrap_or_else(|error| panic!("size {n}: {}", error.message()));
        // Index publication is O(log N) per delta, separately covered by
        // private ownership publication/withdrawal scaling. Keep this check
        // sensitive to a single extra visit per parameter pair in lowering.
        let footprint_work: usize = events
            .iter()
            .filter_map(|event| match event {
                crate::instrumentation::VerificationEvent::OperationFinished {
                    name, work, ..
                } if name == "prepare ownership footprint" => Some(*work),
                _ => None,
            })
            .sum();
        work - footprint_work
    };
    work(1);
    sizes.map(|n| (n, work(n)))
}

/// A function's entry lowers each requirement reading only the parameters
/// it names (roadmap/scaling.md, cause 8), so the work to verify a function
/// that owns one object per parameter grows with the parameters, not with
/// their square. Sizes double, so past the fixed cost of a verification the
/// second increment is about twice the first when the entry is linear and
/// four times it when the entry is quadratic.
#[test]
fn entry_setup_is_linear_in_owned_parameters() {
    let samples = owned_parameter_entry_work([16, 32, 64]);
    let linear = |samples: &[(usize, usize); 3]| {
        let first = samples[1].1 - samples[0].1;
        let second = samples[2].1 - samples[1].1;
        second * 2 <= first * 5 && second <= first * 2 + 128
    };
    eprintln!("owned parameter entry work: {samples:?}");
    assert!(linear(&samples), "{samples:?}");
    // Smaller programs must still expose one extra visit per parameter pair,
    // even when the rest of entry setup has a large linear cost.
    let paired = samples.map(|(size, work)| (size, work + size * size));
    assert!(
        !linear(&paired),
        "the entry fixture must detect quadratic work: {samples:?}"
    );
}

/// A function of `n` parameters whose proof states one fact about one of
/// them: the `have` reads `s` and `a0` and nothing else.
fn many_parameters(n: usize) -> (String, String) {
    let params = (0..n)
        .map(|i| format!("int32 a{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let c = format!(
        "int32 caller({params}) {{
    int32 s;
    s = a0;
    return s;
}}"
    );
    let click = format!(
        "verifying \"hunt.c\";

int32 caller({params}) {{
    ensures result == a0 by {{
        step();
        step();
        have s == a0 by {{ close(); }}
        step();
        close();
    }}
}}"
    );
    (c, click)
}

// Lowering a proof-side proposition must build the environment of the names
// it reads, not of every parameter and local: a function of N parameters and
// N such steps otherwise costs N^2.
#[test]
fn a_have_ignores_unrelated_parameters() {
    let work = [2, 32].map(|n| {
        let (c, click) = many_parameters(n);
        let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
            verify_c_sources(&click, &[("hunt.c", c.as_str())])
        });
        result.unwrap_or_else(|error| panic!("many_parameters at {n}: {}", error.message()));
        samples
            .iter()
            .filter(|sample| sample.tactic.tactic_name == "have")
            .map(|sample| sample.work)
            .max()
            .expect("the `have` reports its work")
    });
    assert!(
        work[1] <= work[0] + band(work[0]),
        "many_parameters: the `have` grows from {} to {} between 2 and 32 parameters \
         (roadmap/scaling.md)",
        work[0],
        work[1]
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: reduced full-proof setup took 2.8s; larger fixture hit the 30s gate limit"]
fn saved_iterated_base_ignores_aliases_states_and_unrelated_resources() {
    let (source, sources) =
        super::expansion_tests::mdtest_sources("mdtests/iterated_saved_base_release.md");
    // Exact work equality detects a scan even at these small sizes. Larger
    // parameter sets mostly measure full-function setup before indexed `fold`.
    let work = [1, 2, 4].map(|size| {
        let parameters = (0..size)
            .map(|i| format!(", int32* alias{i}, int32* spare{i}"))
            .collect::<String>();
        let signature = format!("int32 index{parameters})");
        let c = sources[0].1.replace("int32 index)", &signature);
        let mut click = source.replace("int32 index)", &signature);
        let requirements = (0..size)
            .map(|i| format!("    requires alias{i} == data;\n    owns spare{i}[0..1];\n"))
            .collect::<String>();
        click = click.replace(
            "    requires 0 <= index;",
            &format!("{requirements}    requires 0 <= index;"),
        );
        let marks = (0..size)
            .map(|i| format!("    mark unrelated{i};\n"))
            .collect::<String>();
        click = click.replace("    mark before;", &format!("{marks}    mark before;"));
        // The two unfolds, the mark, and the step precede the indexed fold.
        let indexed_fold = 4 + size;
        let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
            verify_c_sources(&click, &[(sources[0].0.as_str(), c.as_str())])
        });
        result.unwrap_or_else(|error| panic!("size {size}: {}", error.message()));
        let successful = samples
            .iter()
            .filter(|sample| {
                sample.tactic.tactic_name == "fold" && sample.tactic.source_index == indexed_fold
            })
            .map(|sample| sample.work)
            .max()
            .expect("indexed fold work");
        let false_guard = c.replace("occupied[index] = 0", "occupied[index] = 1");
        let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
            verify_c_sources(&click, &[(sources[0].0.as_str(), false_guard.as_str())])
        });
        assert!(result.unwrap_err().message().contains("the guard is false"));
        let refused = samples
            .iter()
            .filter(|sample| {
                sample.tactic.tactic_name == "fold" && sample.tactic.source_index == indexed_fold
            })
            .map(|sample| sample.work)
            .max()
            .expect("refused indexed fold work");
        (successful, refused)
    });
    assert_eq!(work[0], work[1], "saved-base work: {work:?}");
    assert_eq!(work[1], work[2], "saved-base work: {work:?}");
}

#[test]
fn named_unfold_beside_views_scales_with_the_opened_delta() {
    let mut totals = Vec::new();
    for count in [4, 8, 16] {
        let parameters = lines(count, |i| format!("int32* p{i},"));
        let owned = lines(count, |i| format!("consumes r{i}: owner(p{i});"));
        let opens = lines(count, |i| format!("let {{ unused: m{i} }} = unfold(r{i});"));
        let c = format!("void check({parameters} int32* q) {{}}");
        let proof = format!(
            r#"
            resource owner(p: int32*) {{ field unused: int32; owns p[0..1]; }}
            verifying "hunt.c";
            void check({parameters} int32* q) {{ views q[0..1]; {owned} }} by {{
                {opens}
                have separate(memory(p0[0..1]), memory(q[0..1])) by {{ close(); }}
                step_until(function.exit);
            }}
        "#
        );
        let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
            verify_c_sources(&proof, &[("hunt.c", c.as_str())])
        });
        result.unwrap_or_else(|error| panic!("count {count}: {}", error.message()));
        let work = samples
            .iter()
            .filter(|sample| sample.tactic.tactic_name == "unfold")
            .map(|sample| sample.work)
            .collect::<Vec<_>>();
        assert_eq!(work.len(), count);
        totals.push(work.iter().sum::<usize>());
    }
    assert!(
        totals.windows(2).all(|pair| pair[1] <= pair[0] * 3),
        "{totals:?}"
    );
}

#[test]
fn named_unfold_and_refold_witness_ignore_unrelated_facts() {
    let work = [8, 32, 128].map(|count| {
        let unrelated = lines(count, |i| format!("requires n != {i};"));
        let proof = format!(
            r#"
            verifying "open.c";
            resource owner(p: int32*) {{
                field tag: int32;
                let base: int32* where base == p;
            }}
            void check(int32* p, int32 n) {{
                {unrelated}
                owns r: owner(p);
            }} by {{
                let {{ base: q }} = unfold(r);
                have q == p by close();
                fold(r);
            }}
        "#
        );
        let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
            verify_c_sources(&proof, &[("open.c", "void check(int32* p, int32 n) {}")])
        });
        result.unwrap_or_else(|error| panic!("with {count} facts: {}", error.report()));
        ["unfold", "fold"].map(|tactic| {
            samples
                .iter()
                .find(|sample| sample.tactic.tactic_name == tactic)
                .unwrap_or_else(|| panic!("the named {tactic} is measured"))
                .work
        })
    });
    assert!(
        work.iter()
            .all(|[unfold, fold]| *unfold <= work[0][0] + 16 && *fold <= work[0][1] + 16),
        "unrelated fact work: {work:?}"
    );
}

/// Compare the same explicit observations and C parameters, with and without
/// other same-shaped owners. Parameter/lowering cost is shared by the control;
/// this regression isolates owner selection, also measured directly in the kernel.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: same-shape observation scaling and parameter control"]
fn observing_one_composite_ignores_same_shape_owners() {
    let mut curves = Vec::new();
    for count in [4usize, 16, 64] {
        let parameters = (0..count)
            .map(|i| format!("int32* p{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let last = count - 1;
        let observations = lines(count, |_| format!("observe(cell(p{last}));"));
        let c = format!("void check({parameters}) {{}}");
        let mut runs = Vec::new();
        for crowded in [false, true] {
            let owners = if crowded {
                lines(count, |i| format!("owns cell(p{i});"))
            } else {
                format!("owns cell(p{last});")
            };
            let proof = format!(
                r#"
                resource cell(p: int32*) {{ owns p[0..1]; }}
                verifying "hunt.c";
                void check({parameters}) {{ {owners} }} by {{ {observations} step(); }}
            "#
            );
            let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
                verify_c_sources(&proof, &[("hunt.c", c.as_str())])
            });
            result.unwrap_or_else(|error| {
                panic!("count {count}, crowded {crowded}: {}", error.message())
            });
            let work = samples
                .iter()
                .filter(|sample| sample.tactic.tactic_name == "observe")
                .map(|sample| sample.work)
                .collect::<Vec<_>>();
            assert_eq!(work.len(), count);
            runs.push(work);
        }
        curves.push((
            count,
            runs[0][0],
            runs[0][1],
            runs[1][0],
            runs[1][1],
            runs[1].iter().sum::<usize>(),
        ));
        assert!(
            runs[0]
                .iter()
                .zip(&runs[1])
                .all(|(control, crowded)| *crowded <= *control + 64),
            "same-shape owners add checking work: {curves:?}"
        );
    }
    eprintln!("observe (N, control first/repeat, crowded first/repeat, crowded total): {curves:?}");
}

/// One held owner and a fixed proof: unused function parameters must not add
/// work to each observation. Keep the selected parameter's spelling fixed.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: observation parameter scaling"]
fn observing_one_owner_ignores_unused_parameters() {
    let mut curves = Vec::new();
    for count in [4usize, 16, 64] {
        let parameters = std::iter::once("int32* selected".to_string())
            .chain((1..count).map(|i| format!("int32* unused{i}")))
            .collect::<Vec<_>>()
            .join(", ");
        let c = format!("void check({parameters}) {{}}");
        let proof = format!(
            r#"
            resource cell(p: int32*) {{ owns p[0..1]; }}
            verifying "observe.c";
            void check({parameters}) {{ owns cell(selected); }} by {{
                observe(cell(selected));
                observe(cell(selected));
                observe(cell(selected));
                step();
            }}
            "#
        );
        let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
            verify_c_sources(&proof, &[("observe.c", c.as_str())])
        });
        result.unwrap_or_else(|error| panic!("{count} parameters: {}", error.message()));
        let work = samples
            .iter()
            .filter(|sample| sample.tactic.tactic_name == "observe")
            .map(|sample| sample.work)
            .collect::<Vec<_>>();
        assert_eq!(work.len(), 3);
        curves.push((count, work));
    }
    eprintln!("one-owner observation (parameters, cold/repeated/repeated work): {curves:?}");
    assert!(
        curves.windows(2).all(|pair| pair[0]
            .1
            .iter()
            .zip(&pair[1].1)
            .all(|(small, large)| *large <= *small + 32)),
        "observations walk unused parameters: {curves:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: have opening composition scaling"]
fn have_opening_does_not_copy_ambient_compositions() {
    let (source, sources) = super::expansion_tests::mdtest_sources(
        "mdtests/a_cast_contract_a_saved_word_keeps_its_historical_relationship.md",
    );
    let mut curves = Vec::new();
    for size in [4, 16, 64] {
        let parameters = (0..size)
            .map(|i| format!(", int32* unused{i}"))
            .collect::<String>();
        let owners = (0..size)
            .map(|i| format!("owns *unused{i};\n"))
            .collect::<String>();
        let proof = source
            .replace("struct node* p)", &format!("struct node* p{parameters})"))
            .replace("owns *slot;", &format!("owns *slot;\n{owners}"));
        let sources = sources
            .iter()
            .map(|(name, text)| {
                (
                    name.clone(),
                    text.replace("struct node* p)", &format!("struct node* p{parameters})")),
                )
            })
            .collect::<Vec<_>>();
        let borrowed = sources
            .iter()
            .map(|(n, s)| (n.as_str(), s.as_str()))
            .collect::<Vec<_>>();
        let (result, samples) =
            crate::instrumentation::collect_tactic_work(|| verify_c_sources(&proof, &borrowed));
        result.unwrap_or_else(|error| panic!("{size}: {}", error.report()));
        let selected = samples
            .iter()
            .find(|s| s.tactic.tactic_name == "have")
            .unwrap();
        curves.push(selected.work);
    }
    eprintln!("have composition work: {curves:?}");
    assert!(
        curves.windows(2).all(|p| p[1] <= p[0] + 32),
        "have copied ambient compositions: {curves:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: explicit pointer separation beside aliases"]
fn explicit_pointer_separation_ignores_ambient_aliases() {
    let (source, sources) = super::expansion_tests::mdtest_sources(
        "mdtests/explicit_partition_separation_proves_pointer_distinctness.md",
    );
    let mut curves = Vec::new();
    for size in [4, 16, 64] {
        let parameters = (0..size)
            .map(|i| format!(", int32* a{i}"))
            .collect::<String>();
        let requirements = (0..size)
            .map(|i| format!("requires a{i} == p;\n"))
            .collect::<String>();
        let proof = source
            .replace("int32* q)", &format!("int32* q{parameters})"))
            .replace("owns *q;", &format!("owns *q;\n{requirements}"));
        let sources = sources
            .iter()
            .map(|(name, text)| {
                (
                    name.clone(),
                    text.replace(
                        "int *q)",
                        &format!("int *q{})", parameters.replace("int32", "int")),
                    ),
                )
            })
            .collect::<Vec<_>>();
        let borrowed = sources
            .iter()
            .map(|(n, s)| (n.as_str(), s.as_str()))
            .collect::<Vec<_>>();
        let (result, samples) =
            crate::instrumentation::collect_tactic_work(|| verify_c_sources(&proof, &borrowed));
        result.unwrap_or_else(|e| panic!("{size}: {}", e.report()));
        let work = samples
            .iter()
            .filter(|s| s.tactic.tactic_name == "have")
            .map(|s| s.work)
            .collect::<Vec<_>>();
        assert_eq!(work.len(), 2);
        curves.push((size, work));
    }
    eprintln!("explicit pointer separation source work: {curves:?}");
    assert!(
        curves
            .windows(2)
            .all(|p| p[0].1.iter().zip(&p[1].1).all(|(a, b)| *b <= *a + 4)),
        "explicit separation grows with aliases: {curves:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: active borrow alias scaling"]
fn one_write_with_a_borrow_does_not_walk_unrelated_aliases() {
    let mut curves = Vec::new();
    for viewed in [false, true] {
        for size in [4, 16, 64] {
            let parameters = (0..size)
                .map(|i| format!(", int32* a{i}"))
                .collect::<String>();
            let requirements = (0..size)
                .map(|i| format!("requires a{i} == p;\n"))
                .collect::<String>();
            let c = format!("void set(int32* p, int32* q{parameters}) {{ *p = 1; }}");
            let view = if viewed { "views *q;" } else { "" };
            let proof = format!(
                "verifying \"borrow.c\";\nvoid set(int32* p, int32* q{parameters}) {{ owns *p; {view} {requirements} }} by {{ step(); }}"
            );
            let proof = if viewed {
                proof.replace(
                    "by { step(); }",
                    "by { have separate(memory(*p), memory(*q)) by { close(); } step(); }",
                )
            } else {
                proof
            };
            let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
                verify_c_sources(&proof, &[("borrow.c", &c)])
            });
            result.unwrap_or_else(|e| panic!("viewed={viewed}, aliases={size}: {}", e.report()));
            let work = samples
                .iter()
                .find(|s| s.tactic.tactic_name == "step")
                .unwrap()
                .work;
            curves.push((viewed, size, work));
        }
    }
    eprintln!("write beside one borrow (active, aliases, work): {curves:?}");
    for samples in curves.chunks(3) {
        assert!(
            samples
                .iter()
                .all(|(_, _, work)| *work <= samples[0].2 + 16),
            "write scans aliases with fixed owner and borrow: {samples:?}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: call composition retention at three alias counts and two borrow shapes"]
fn retaining_call_compositions_ignores_unused_aliases() {
    for borrowed in [2, 4] {
        let mut samples = Vec::new();
        for count in [4, 16, 64] {
            let params = (0..count)
                .map(|i| format!("int32* q{i}"))
                .collect::<Vec<_>>()
                .join(", ");
            let requires = lines(count, |i| format!("requires q{i} == data;"));
            let c = format!("void caller(int32* data, int32* other, {params}) {{ touch(data); }}");
            let click = format!(
                r#"
                verifying "hunt.c";
                extern void touch(int32* data) {{ owns data[0..{borrowed}]; }}
                void caller(int32* data, int32* other, {params}) {{
                    owns data[0..4]; owns *other;
                    {requires}
                }} by {{ step(); step(); }}
            "#
            );
            let (result, events) = crate::instrumentation::collect(|| {
                verify_c_sources(&click, &[("hunt.c", c.as_str())])
            });
            result.unwrap();
            let work = events
                .iter()
                .filter_map(|event| match event {
                    crate::instrumentation::VerificationEvent::OperationFinished {
                        name,
                        work,
                        ..
                    } if name == "call entry composition retention" => Some(*work),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert!(!work.is_empty(), "the call exercised composition retention");
            samples.push((count, *work.iter().max().unwrap()));
        }
        eprintln!("borrow {borrowed} composition-retention work: {samples:?}");
        assert!(
            samples.iter().all(|(_, work)| *work == samples[0].1),
            "{samples:?}"
        );
    }
}

/// Unfolding retains the opaque predicate as well as its body. Loop entry
/// must retain that context too, rather than delete the atom and rebuild it.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: sequential unfolded loops at three sizes"]
fn unfolded_loop_predicates_retain_the_fact_context() {
    fn unfolded_loops(n: usize) -> (String, String) {
        let (c, click) = loops(n);
        let click = click
            .replace(
                "int32 caller",
                "predicate reflexive(x: int32) { x == x }\nint32 caller",
            )
            .replace("owns p[0..4];", "owns p[0..4]; requires reflexive(0);")
            .replace("} by {", "} by { unfold(reflexive(0));");
        (c, click)
    }
    let counts = [3, 6, 12].map(|n| {
        let before = crate::kernel::reasoning::path_facts::context_rebuild_entries();
        run(unfolded_loops, n);
        crate::kernel::reasoning::path_facts::context_rebuild_entries() - before
    });
    eprintln!("unfolded loop context entries: {counts:?}");
    let early = (counts[1] - counts[0]) / 3;
    let late = (counts[2] - counts[1]) / 6;
    assert!(
        late <= early + band(early),
        "unfolded predicates cause growing context rebuilds per loop: {counts:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: memory observation parameter and ownership scaling"]
fn observing_one_memory_range_ignores_unrelated_parameters_and_owners() {
    for owners in [false, true] {
        let mut curves = Vec::new();
        for count in [4usize, 16, 64] {
            let parameters = std::iter::once("int32* selected".to_string())
                .chain((1..count).map(|i| format!("int32* unused{i}")))
                .collect::<Vec<_>>()
                .join(", ");
            let extra = if owners {
                (1..count)
                    .map(|i| format!("owns unused{i}[0..1];"))
                    .collect::<Vec<_>>()
                    .join(" ")
            } else {
                String::new()
            };
            let c = format!("void check({parameters}) {{}}");
            let proof = format!(
                r#"
                verifying "observe.c";
                void check({parameters}) {{ owns selected[0..1]; {extra} }} by {{
                    observe(selected[0..1]);
                    observe(selected[0..1]);
                    observe(selected[0..1]);
                    step();
                }}
            "#
            );
            let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
                verify_c_sources(&proof, &[("observe.c", c.as_str())])
            });
            result.unwrap_or_else(|error| panic!("{count} / {owners}: {}", error.report()));
            let work = samples
                .iter()
                .filter(|sample| sample.tactic.tactic_name == "observe")
                .map(|sample| sample.work)
                .collect::<Vec<_>>();
            assert_eq!(work.len(), 3);
            curves.push(work);
        }
        assert!(
            curves.windows(2).all(|pair| pair[0]
                .iter()
                .zip(&pair[1])
                .all(|(small, large)| *large <= *small + 32)),
            "owners={owners}: {curves:?}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: explicit named-instance observation with redundant owners"]
fn observing_one_instance_ignores_unrelated_instances() {
    let work = [4, 16, 64].map(|count| {
        let parameters = (0..count)
            .map(|i| format!(", int32* spare{i}"))
            .collect::<String>();
        let signature = format!("void check(int32* selected{parameters})");
        let held = (0..count)
            .map(|i| format!("owns spare_owner{i}: cell(spare{i});"))
            .collect::<String>();
        let c = format!("{signature} {{ int32 scratch; scratch = 1; }}");
        let proof = format!(
            r#"
            verifying "observe.c";
            resource cell(p: int32*) {{ field tag: int32; owns p[0..1]; fact *p == tag; }}
            {signature} {{ owns chosen: cell(selected); {held} }} by {{
                step(); step();
                observe(chosen);
                step();
            }}
            "#,
        );
        let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
            verify_c_sources(&proof, &[("observe.c", c.as_str())])
        });
        result.unwrap_or_else(|error| panic!("{count}: {}", error.report()));
        samples
            .iter()
            .find(|sample| sample.tactic.tactic_name == "observe")
            .expect("named observation was measured")
            .work
    });
    assert!(
        work.windows(2).all(|pair| pair[1] <= pair[0] + 32),
        "{work:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: saved memory observation parameter, alias, ownership and state scaling"]
fn observing_saved_memory_ignores_aliases_states_and_unrelated_owners() {
    for owned in [false, true] {
        let mut curves = Vec::new();
        for count in [1, 2, 4] {
            let parameters = (0..count)
                .map(|i| format!(", int32* alias{i}, int32* spare{i}"))
                .collect::<String>();
            let requirements = (0..count)
                .map(|i| format!("requires alias{i} == selected; owns spare{i}[0..1];"))
                .collect::<String>();
            let marks = (0..count)
                .map(|i| format!("mark unrelated{i};"))
                .collect::<String>();
            let owner = if owned {
                "owns selected[index..index + 1];"
            } else {
                ""
            };
            let c = format!(
                "void check(int32* selected, int32 index{parameters}) {{ int32 scratch; scratch = 1; }}"
            );
            let proof = format!(
                r#"
                verifying "observe.c";
                void check(int32* selected, int32 index{parameters}) {{ requires 0 <= index; requires index < 64; {owner} {requirements} }} by {{
                    {marks}
                    mark before;
                    step(); step();
                    observe(at(before, selected)[index..index + 1]);
                    observe(at(before, selected)[index..index + 1]);
                    step();
                }}
            "#
            );
            let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
                verify_c_sources(&proof, &[("observe.c", c.as_str())])
            });
            if owned {
                result.unwrap_or_else(|error| panic!("{count}: {}", error.report()));
            } else {
                assert!(result.unwrap_err().message().contains("exact memory range"));
            }
            let work = samples
                .iter()
                .filter(|sample| sample.tactic.tactic_name == "observe")
                .map(|sample| sample.work)
                .collect::<Vec<_>>();
            assert_eq!(work.len(), if owned { 2 } else { 1 });
            curves.push(work);
        }
        assert!(
            curves.windows(2).all(|pair| pair[0]
                .iter()
                .zip(&pair[1])
                .all(|(small, large)| *large <= *small + 32)),
            "owned={owned}: {curves:?}"
        );
    }
}
