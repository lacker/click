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
        }} then {{
            step();
            have 0 <= s by {{ solve(); }}
            have s <= {bound} by {{ solve(); }}
        }} else {{
            have s <= {bound} by {{ solve(); }}
        }}"
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
        solve();
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
    solve();
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

fn run(shape: fn(usize) -> (String, String), n: usize) -> Run {
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
fn pointer_field_links_cost_the_same_at_every_position() {
    assert_no_drift("deep_chain", deep_chain, 12);
}

#[test]
fn straight_line_assignments_cost_the_same_at_every_position() {
    assert_no_drift("straight_line", straight_line, 12);
}

#[test]
fn constant_index_stores_cost_the_same_at_every_position() {
    assert_no_drift("const_array", const_array, 12);
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

// Splitting a caller's owner must not enumerate the other parameter owners
// that happen to share its external-argument memory block.
#[test]
fn a_partial_borrow_call_ignores_unrelated_owned_objects() {
    assert_flat_across(
        "partial_borrow_beside_objects",
        partial_borrow_beside_objects,
        [1, 8],
        "touch_half(data);",
    );
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
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            verify_c_sources(&click, &[("hunt.c", c.as_str())])
        });
        result.unwrap_or_else(|error| panic!("size {n}: {}", error.message()));
        work
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
        have s == a0 by {{ solve(); }}
        step();
        solve();
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
#[ignore = "nightly: reduced full-proof setup took 2.8s; larger fixture hit the 30s gate limit"]
fn saved_iterated_base_ignores_aliases_states_and_unrelated_resources() {
    let (source, sources) =
        super::expansion_tests::mdtest_sources("mdtests/iterated_saved_base_release.md");
    // Exact work equality detects a scan even at these small sizes. Larger
    // parameter sets mostly measure full-function setup before `give`.
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
        let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
            verify_c_sources(&click, &[(sources[0].0.as_str(), c.as_str())])
        });
        result.unwrap_or_else(|error| panic!("size {size}: {}", error.message()));
        let successful = samples
            .iter()
            .filter(|sample| sample.tactic.tactic_name == "give")
            .map(|sample| sample.work)
            .max()
            .expect("give work");
        let false_guard = c.replace("occupied[index] = 0", "occupied[index] = 1");
        let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
            verify_c_sources(&click, &[(sources[0].0.as_str(), false_guard.as_str())])
        });
        assert!(result.unwrap_err().message().contains("the guard is false"));
        let refused = samples
            .iter()
            .filter(|sample| sample.tactic.tactic_name == "give")
            .map(|sample| sample.work)
            .max()
            .expect("refused give work");
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
                have separate(memory(p0[0..1]), memory(q[0..1])) by {{ solve(); }}
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

/// Compare the same explicit observations and C parameters, with and without
/// other same-shaped owners. Parameter/lowering cost is shared by the control;
/// this regression isolates owner selection, also measured directly in the kernel.
#[test]
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
#[ignore = "nightly: active loan alias scaling"]
fn one_write_with_a_loan_does_not_walk_unrelated_aliases() {
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
                "verifying \"loan.c\";\nvoid set(int32* p, int32* q{parameters}) {{ owns *p; {view} {requirements} }} by {{ step(); }}"
            );
            let proof = if viewed {
                proof.replace(
                    "by { step(); }",
                    "by { have separate(memory(*p), memory(*q)) by { known(); } step(); }",
                )
            } else {
                proof
            };
            let (result, samples) = crate::instrumentation::collect_tactic_work(|| {
                verify_c_sources(&proof, &[("loan.c", &c)])
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
    eprintln!("write beside one loan (active, aliases, work): {curves:?}");
    for samples in curves.chunks(3) {
        assert!(
            samples
                .iter()
                .all(|(_, _, work)| *work <= samples[0].2 + 16),
            "write scans aliases with fixed owner and loan: {samples:?}"
        );
    }
}

#[test]
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
            .replace("} by {", "} by { unfold(reflexive);");
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
