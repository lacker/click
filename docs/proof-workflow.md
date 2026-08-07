# Proof Workflow

Click proofs live in `by` clauses.

When a proof does not close, first determine whether the claim is false, the
proof needs explicit supported steps, or Click has a language, correctness, or
tooling defect. The [proof-failure triage guide](advanced/proof-failure-triage.md)
gives the canonical classification and reduction workflow. In particular, a
prompt failure from an incomplete smart tactic is not by itself an engine bug.

## Proof Kinds

A **pure proof** derives a proposition from facts at one execution point. It
does not execute C, move between program points, or transform resource facts.
Pure theorem proofs and the nested proof inside `have ... by { ... }` are pure
proofs.

An **execution proof** establishes a relationship between the entry and exit of
a code region. It owns an execution frontier consisting of the current program
point, symbolic C state, pure facts, resource facts, and pending control-flow
continuations. Execution steps move that frontier forward. Pure reasoning and
resource reasoning may occur between execution steps without moving it.

A function-contract proof is therefore an execution proof even when some of
its individual steps are pure. Loop initialization is a pure proof at the loop
entry; loop preservation is an execution proof of one arbitrary iteration.
Together they justify the loop rule used by the execution proof of the
enclosing function region.

For contracts with several claims, a trailing `by { ... }` block is one
grouped execution proof of the function contract:

```click
int32 set_first(int32 p[], int32 value) {
    owns p[0..1];
    mutable p[0..1];
    ensures result == value;
    ensures p[0] == value;
} by {
    execute();
    frame();
    simp();
}
```

Click replays the C region once. Every effect and postcondition is then checked
against the resulting shared proof state. Goal-specific closing steps still
have their normal roles: `frame()` closes effect goals, and `simp()` or
resource reasoning closes postconditions. Per-claim proof clauses remain
available for independent proofs, but cannot be mixed with a grouped proof in
the same function.

The shorthand `} by auto;` builds one deterministic grouped script:
`execute()`, declared loop checks, `frame()` when the contract has effects,
and `simp()` when it has postconditions. Composite-resource folds and theorem
applications remain explicit.

After execution reaches the return frontier, grouped tactics retain source
order. `fold`, `apply`, and `have` transform the current finalized path;
`frame()` closes the effect goals then provable, and `simp()` closes the
postconditions then provable. A later fact or fold does not retroactively affect
an earlier closing step. Each symbolic path is finalized once, and every
contract certificate is packaged from that same finalized specification.

## Tactics

Currently accepted tactics:

```click
by auto;
by simp;
by frame;
```

Omitting a proof clause uses `auto`. `by simp;` means the same operation as
`by simp;`, and `by frame;` means the same operation as
`by { frame(); }`. All four forms act at the current proof frontier; neither
`simp` nor `frame` implicitly executes C. See the
[proof tactics reference](proof-tactics.md).

For an individual claim, `auto` is the broad orchestration tactic. It first
tries verification execution, then may try the smart `execute()` proof
script and records the tactics that succeeded. Grouped `auto` has the fixed
expansion described above, so grouped proofs do not depend on proof search.

`simp` is a smart contextual simplifier. It is useful for straight-line
postconditions and unfolded predicate goals. It simplifies logical connectives,
constant/reflexive integer comparisons, small arithmetic forms, concrete folds,
and several kernel equality patterns. For order goals, it also rewrites through
known equalities, evaluates equality-linked constant arithmetic, and uses the
discrete relationship between strict and non-strict integer bounds.

Bare `frame()` (including `by frame;`) performs smart contextual range
reasoning. The simple exact form is `frame() using { P; ... }`.

The exhaustive simple/smart classification is in the
[proof tactics reference](proof-tactics.md).

## Explicit Proof Scripts

Explicit proof scripts use function-call-shaped tactics:

```click
by {
    execute();
    unfold(sorted);
    simp();
}
```

Current tactics. The [proof tactics reference](proof-tactics.md) is the
authoritative inventory and classifies each spelling as simple, smart, or
control flow.

- `step() using { P; ... }`: advance one small C transition using exactly
  the listed execution premises. It does not automatically transport memory-dependent facts to
  the new snapshot; use `transport(source, target)` explicitly. At a C `if`, an
  exact condition fact selects and enters one arm. At a loop head, it evaluates
  the condition once and enters one iteration or advances past the loop.
- `step();`: execute one small C transition from the current execution
  point with contextual prerequisite reasoning and automatic supported fact
  transport. It uses the same branch and loop-head transitions as
  `step() using`.
- `execute();`: build symbolic verification paths from the current
  execution point to function exit. From function entry, this executes the
  whole C0 function. It applies verified abstract loop rules where available.
  Requirements of opaque calls may be routine consequences of current facts;
  smart execution retains a checked proposition derivation for each such
  premise, and expansion emits the corresponding exact source-level facts.
  Equivalent field loads remain matchable when harmless materialization gives
  them different memory-snapshot spellings.
- `execute_until(statement(N));`: execute the current deterministic prefix up
  to the entry of statement region `N`. It can cross verified loops, but an
  unresolved `if` still requires explicit branch entry. It composes with prior
  execution steps and joined branches. The target must be
  forward and reachable on the current execution path, and each source step
  must produce exactly one normal successor.
- `loop { ... }`: verify the loop exactly at the current frontier and advance
  to its checked abstract exit. Its nested `initialize`, `preserve`, invariant,
  and effect clauses construct the kernel rule; it never seeks to a numbered
  source loop.
- `close_invariants();`: discharge a loop's whole invariant bundle at the back
  edge. It is accepted only inside `preserve by { ... }`, and at most once per
  path. Omitting it makes Click append the closer implicitly.
- `frame();`: smart contextual frame reasoning for the current function or
  active structural-effect goal.
- `frame() using { P; ... }` and the region form: the simple exact-premise
  frame check. Expansion always emits this form.
- `unfold(name);`: unfold matching predicate facts and goals.
- `unfold(resource);`: consume one owned composite resource fact and expose its
  immediate body facts.
- `fold(resource);`: require every declared pure body fact exactly (or by
  context-free normalization), consume one immediate composite body, and
  rebuild the owned composite resource fact. Establish derived facts with
  `have` before folding.
- `apply(theorem_name(args...));`: instantiate one verified pure theorem from
  the standard library or current file. Every requirement must be an exact
  current fact or normalize to true without context; the step does not search
  for a derivation. It adds the theorem's conclusions and never changes the
  resource context. This bare spelling is smart because its premises come from
  the ambient context.
- `apply(theorem_name(args...)) using { P; ... }`: the simple spelling,
  drawing premises only from the listed facts. Expansion rewrites bare `apply`
  into this form.
- `have proposition by { ... }`: run a scoped pure proof and add its proposition
  to the current pure facts. The nested proof accepts
  `unfold`, `apply`, `choose`, `witness`, `simp`, nested `have`, and proof-level
  `if` case analysis; it cannot execute C or transform resources. Both `if`
  branches prove the local proposition, after which the surrounding proof
  continues. After execution reaches function exit, Click proves the `have`
  proposition independently on every completed execution path and adds the
  resulting fact to that path's pure facts.
- `if proposition { ... } else { ... }`: prove the current claim twice, once
  with the proposition added to the pure facts and once with its negation
  added. Each branch has its own proof script; the common continuation then
  runs in every feasible case. It does not execute a C `if` statement.
- `observe(resource);`: project one view step from a held composite resource
  fact. This exposes immediate pure facts and viewed immediate contained
  resource facts without exposing owned contained permissions.
- `choose(k from requirement name);`: open a named existential precondition,
  introducing proof-local int32 value `k`.
- `choose(k from requirement N);`: the same operation by zero-based requirement
  index. Prefer labels for durable scripts.
- `witness(k = expression);`: prove the current existential goal by substituting
  the given int32 expression for binder `k`.
- `assumption();`: close an exact current pure goal.
- `normalize();`: close a pure goal by context-free computation.
- `rewrite(equality);`: rewrite a pure goal once using an exact available int32
  equality whose left side is a variable.
- `transport(source, target);`: require an exact source fact and apply one
  certified atomic transport rule to establish the stated target fact at the
  current statement frontier. Conditions use framing; structural memory facts
  such as `loadable(...)` use the certified execution effects. Like `apply`,
  this bare spelling is smart.
- `transport(source, target) using { P; ... }`: the simple, exact-premise
  spelling of the same rule.
- `derive using { Q; ... }`: close the current atomic goal using Click's
  deterministic atomic theories and exactly the listed premises.
- `intro();`, `split();`, `left();`, `right();`, `contradiction(P);`: one
  structural logical rule each. They are
  accepted only while a pure goal is active, typically inside `have ... by` or
  a theorem proof.
- `simp();`: request smart contextual simplification when the proof block is
  checked.

The end of a per-claim `by { ... }` block checks that claim. The end of a
trailing grouped function block checks every effect and postcondition in the
contract.

When the execution frontier is a C `if`, use `branch`:

```click
branch {
    then {
        step(); // Execute the first statement in the C then arm.
    }
    else {
        step(); // Execute the first statement in the C else arm.
    }
}
```

`branch` reads and consumes the C guard at the frontier. Ordinary `step()`
calls handle statements inside each arm. The arm states join at the shared C
continuation, and the following proof runs once. A nested C `if` uses another
`branch` when it reaches the frontier.

At every linear execution frontier there is exactly one current proof state.
The arm states created by `branch` are temporary subproofs, not persistent
path-sensitive continuations. Completed arms that return are retained only as
function outcomes; later tactics do not execute in them.

Add `ensuring` when branch-local execution should establish a common interface
before the rest of the function proof:

```click
branch {
    ensuring {
        fact y >= 0;
        owns buffer(data, len);
        views metadata(data, len);
    }
    then {
        step();
    }
    else {
        step();
    }
}
step();
```

`statement(N).entry` means immediately before statement region `N` executes.
`statement(N).exit` means immediately after it completes. Lowering assigns
statement IDs globally in source preorder: a compound statement receives its
ID before the statements nested in its arms or body. A sequence itself does
not receive an ID. Structural assertion and loop checks inserted by Click are
not source statements and do not consume IDs. Structural traversal, tactic
execution, snapshots, expansion, and replay all use this same layout. Every
continuing arm must establish every `ensuring` assertion. Exact common facts
and resources remain available automatically; facts about changed state that
the continuation needs must be listed explicitly. Deterministic consequences
of listed resources, such as memory loadability and the view of an owned
resource, remain available.

Arm-only snapshots are not exported. The function-entry state used by
`old(...)` and the common-frontier snapshot remain available. Changed
pointer-valued locals become fresh symbolic pointers at the join. The
interface must export the facts and resources needed to use them, such as
`views selected[0..len]`; symbolic pointers do not imply non-aliasing with
concrete allocations.

For example, pure case analysis needs no C execution:

```click
theorem int32_sign_split(x: int32) {
    ensures x <= 0 or x > 0 by {
        if x <= 0 {
            simp();
        } else {
            simp();
        }
    }
}
```

`unfold(predicate)`, `apply(theorem)`, `have`, and `fold(resource)` update the
current proof context immediately. They can therefore prepare the exact pure
fact or resource fact required by the following `step()` or `fold(resource)`.
Applications after function exit remain path-local, so `result` and post-state
expressions are interpreted separately for each completed path.

Some successful `auto` proofs record replayable tactic certificates when the
current tactic language can express the argument.

An execution proof tracks an execution frontier: the current execution point
together with its enclosing continuation stack. Proof scripts can start at
function entry, advance by one statement with `step();`, unpack a C `if` at the
current frontier with `branch`, replace scoped paths with an explicit abstract
interface using `branch ensuring`, pause at a statement entry with
`execute_until(statement(N));`, and execute to function exit with `execute();`.
Resource steps such as `observe`, `unfold`, and `fold` can happen between those
execution steps.

The execution frontier carries the same global statement ID assigned by
lowering. The source layout uses that ID to identify branch children,
continuations, and nested loops. Checks inserted by annotation lowering remain
attached to their source statement and do not become extra tactics.

Ordinary statement steps and frontier-local `branch` use the same certified
condition and statement transitions. `branch` joins its arm-local frontiers
behind a checked common interface. `execute()` is the batch form that
continues from the same frontier to function exit.

At function entry, `views composite(...)` resource requirements are projected
one step automatically, matching `observe(composite(...))` for immediate
contained views. Owned composite resources still require an explicit
`observe(...)` when a proof wants to read through the folded resource.

Existential tactics are deterministic replay steps, not search tactics. A
typical existential-introduction proof names a witness:

```click
ensures found: (0..n).any(|k| { k == result }) by {
    execute();
    witness(k = 0);
    simp();
}
```

`choose` is existential elimination for facts that are already assumed. The
current source forms are intentionally narrow: `requirement name` means a
`requires name: ...;` label, while `requirement N` means the Nth written
`requires` clause. The selected source must lower to an existential
proposition, either directly or after an explicit `unfold(predicate);` step.

```click
requires has_k: exists (k: int32) { k == x };
ensures again: exists (j: int32) { j == x } by {
    execute();
    choose(k from requirement has_k);
    witness(j = k);
    simp();
}
```

For a predicate requirement that hides an existential, unfold the predicate
first:

```click
requires has_x: bytes_contains(p, 0, n, 'x');
ensures again: bytes_contains(p, 0, n, 'x') by {
    execute();
    unfold(bytes_contains);
    choose(found from requirement has_x);
    witness(k = found);
    simp();
}
```

## Frontier Facts And Loop Proofs

Use `have` to prove an intermediate proposition at the current execution
frontier. Loop proofs likewise operate where the frontier encounters a loop:

```click
by {
    step();
    step();
    have i == 0 by {
        simp();
    }
    loop as fill {
        invariant i >= 0;
        invariant i <= n;
        mutable p[0..n] by frame;

        step {
            mutable p[i..i + 1] by frame;
        }
    }
}
```

`have` does not replay the function prefix. It sees the exact facts and
resources established by preceding `step() using`, `unfold`, `fold`, and other
ordinary proof tactics. It proves its proposition on every active proof path
and adds the resulting fact to the following context.

`statement(N)` selects the Nth source statement code region in structural
order for execution targets and snapshots:

```click
execute_until(statement(4));
have y >= 0 by {
    simp();
}
step();
have at(statement(4).entry, y) >= 0 by {
    assumption();
}
```

`loop as name { ... }` creates entry and exit snapshot names for the loop at
the current frontier; the name is not a selector and never moves the frontier.

A code region is a static source construct with extent, such as a function,
loop, statement, or block. A program point is a proof-relevant boundary or
position in the program, often associated with a code region, such as
`loop_name.entry`. A visit is one runtime arrival at a program point. Visits
are useful semantic language, but they are not currently Click syntax.

Snapshot expressions use visit selectors:

```click
at(function.entry, x)
at(loop_name.entry, x)
at(statement(0).entry, x)
at(statement(0).exit, x)
at(statement(0).entry, p[0] == 7)
at(statement(0).entry, loadable(p[0..n]))
```

`loop_name.entry` is available in invariants on that loop and in its explicit
`preserve` proof. Once the loop tactic succeeds, `loop_name.exit` is available
to the enclosing proof.

Statement entry and exit snapshots are currently recorded by deterministic
proof execution. `step()`, `execute_until(...)`, and `execute()`
record each deterministic boundary they cross. An `at(...)` expression reads
memory, reassigned parameters, and declared scalar, pointer, or array locals
from the selected state. `at(selector, proposition)` instead snapshots the
complete proposition; use this form for state-relative facts such as
`loadable(...)`, where snapshotting only the segment expression would leave the
memory component at the current state. Branch entries can have a unique
snapshot. An explicit loop `preserve` proof binds
`at(loop_name.entry, ...)` to its fresh arbitrary iteration state. Executing a
verified loop records its unique abstract exit as `at(loop_name.exit, ...)`.
Historical iteration visits still require a future selection model.

`invariant` declarations generate obligations at loop program points. The
loop-level `initialize` proof establishes the complete invariant set before the
first iteration. The `preserve` proof assumes that set and the loop condition,
executes one body iteration, and reestablishes the set:

```click
loop {
    invariant 0 <= i and i <= n;
    invariant sorted(p, n);

    initialize by auto;
    preserve by {
        unfold(sorted);
        step();
        simp();
    }
}
```

Either phase may be omitted. Bounded automation attributed to the `loop`
keyword supplies an omitted phase. An explicit preservation proof
runs in a fresh arbitrary-iteration context and must reach the loop back edge
on every proof branch. It can use ordinary tactics, including `have`,
resource operations, proof-level `if`, and branch execution.

An explicit initialization proof is an ordinary pure proof at the actual loop
entry. It can use `apply`, nested `have`, proof-level `if`, `unfold`, and `simp`,
but it cannot execute C or transform resources. A named loop's entry snapshot
is bound while this proof runs. The facts it proves are checked against the
kernel invariant instances before rule construction.

Execution-proof traversal advances forward through the function. When it
encounters a loop, it checks initialization at the current frontier, checks
preservation in a scoped arbitrary-iteration frontier, and advances the
enclosing execution proof with the loop's abstract exit rule. Later and nested
loops are therefore checked in their actual enclosing proof context; Click does not
reconstruct their entry states by executing the function prefix again.

Explicit `initialize` and `preserve` proofs directly supply the two premises for
that abstract exit rule. After initialization establishes every entry invariant
and every preservation branch reaches the back edge with the invariants and
effects reestablished, the kernel constructs the loop exit without proving
either premise again.

That abstract exit is justified by an opaque kernel `VerifiedLoopRule` over the
symbolic loop-entry state and its required assumptions. The `loop` tactic
applies it immediately and advances the enclosing frontier. There is no later
summary tactic and no detached traversal from function entry.

## Loop Effects

Whole-loop effects:

```click
loop {
    mutable p[0..n] by frame;
}
```

Step-relative effects:

```click
loop {
    step {
        mutable p[i..i + 1] by frame;
    }
}
```

Whole-loop mutable segments must use stable names such as parameters. They
cannot depend on locals modified by the loop. Use `step` effects for
iteration-relative footprints.

A whole-loop segment may depend on fields reached through a stable owner, such
as `owner->data[0..owner->len]`. Structural loop setup projects the immediate
core of a held composite resource, so an owned `vector(owner)` can justify
reading those fields without redundant `views` clauses. The verified effect
summary then preserves field values outside the mutable backing range in the
arbitrary loop-head state. The preservation proof must still establish the
effect at every back edge.

Loop effect summaries are reusable. For example, if a loop mutates only
`dst[0..n]` and requirements prove
`separate(memory(dst[0..n]), memory(src[0..n]))`, `auto` can
use that effect summary to prove source-memory postconditions without a
handwritten source-invariance invariant.

## Debugging Failed Proofs

Failure messages usually include:

- guarantee label
- execution path index
- pure facts
- resource facts, when the failing tactic has a current resource context
- remaining proof obligations
- simplified proposition for failed `simp`

Practical approach:

1. Find the failing mdtest and the exact guarantee label.
2. Read pure facts to learn which branch/path failed.
3. If a predicate is still opaque, add `unfold(predicate_name);`.
4. If memory preservation is missing, check `loadable`, `separate(memory(...))`,
   `immutable`, `mutable`, and loop effects.
5. If arithmetic overflow appears, add numeric requirements or invariants.
6. If the proof needs a general new pattern, add a focused mdtest and then a
   deterministic kernel/proof rule.
