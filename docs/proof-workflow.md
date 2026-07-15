# Proof Workflow

Click proofs live in `by` clauses.

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

## Tactics

Currently accepted tactics:

```click
by auto;
by simp;
by frame;
```

Omitting a proof clause uses `auto`.

`auto` is the broad orchestration tactic. It runs the current symbolic
execution, loop-VC, effect-checking, simplification, and bounded-execution
fallback paths as needed.

`simp` is deterministic local normalization. It is useful for straight-line
postconditions and unfolded predicate goals. It simplifies logical connectives,
constant/reflexive integer comparisons, small arithmetic forms, concrete folds,
and several kernel equality patterns.

`frame` proves `immutable` and `mutable` effect clauses. It rejects ordinary
postconditions.

## Proof-Step Scripts

Deterministic proof scripts use function-call-shaped proof steps:

```click
by {
    execute_rest();
    unfold(sorted);
    simp();
}
```

Current proof steps:

- `execute_step();`: execute one C statement from the current execution point.
  Straight-line statements use their certified transition. An annotated loop
  uses its previously verified abstract loop rule and records the loop entry
  and exit snapshots. The step uses the facts and resources already in the
  proof environment; project or prove needed facts before running it.
- `execute_then_step();`: require the next C statement to be an `if`, prove its
  condition from the current pure facts, and move the execution point to the
  beginning of its then arm without executing the arm body.
- `execute_else_step();`: the corresponding operation for the else arm; it
  proves the C condition false and moves to the beginning of that arm.
- `execute_rest();`: build symbolic verification paths from the current
  execution point to function exit. From function entry, this executes the
  whole C0 function.
- `symbolic_execute();`: legacy spelling for `execute_rest();`.
- `execute_until(statement(N));`: execute the current deterministic prefix up
  to the entry of statement region `N`. It can cross verified loops, but an
  unresolved `if` still requires explicit branch entry. It composes with prior
  execution steps, selected branches, and `advance` joins. The target must be
  forward and reachable on the current execution path, and each source step
  must produce exactly one normal successor.
- `bounded_execute();`: use deterministic bounded execution for concrete-loop
  fallback proofs.
- `loop_vc(loop(N));`: check the generated verification conditions for loop
  code region `N`.
- `frame();`: prove the current function-level effect claim.
- `frame(loop(N));`: prove the effect summary for loop code region `N` and
  expose it for later postcondition reasoning.
- `unfold(name);`: unfold matching predicate facts and goals.
- `unfold(resource);`: consume one owned composite resource fact and expose its
  immediate body facts.
- `fold(resource);`: consume one immediate composite body and rebuild the owned
  composite resource fact.
- `apply(theorem_name(args...));`: perform a pure proof step by instantiating a
  verified pure theorem from the standard library or current file, prove its
  requirements from the current proof context, and add its conclusions as
  derived facts. This step never changes the resource context.
- `have proposition by { ... }`: run a scoped pure proof and add its proposition
  to the current pure facts. The nested proof accepts
  `unfold`, `apply`, `simp`, nested `have`, and proof-level `if` case analysis;
  it cannot execute C or transform resources. Both `if` branches prove the
  local proposition, after which the surrounding proof continues.
- `if proposition { ... } else { ... }`: prove the current claim twice, once
  with the proposition added to the pure facts and once with its negation
  added. Each branch has its own proof script and must finish the current
  claim. A proof-level `if` is therefore the final step in its surrounding
  script unless it is inside `advance`; it does not execute a C `if` statement.
- `advance(program_point) ensuring { ... } by { ... }`: execute the nested
  proof cases to the exact statement entry or exit, checking the listed `fact`,
  `owns`, and `views` assertions in every case. Click then forgets
  branch-specific facts, scalar values, mutable memory, and resources, and
  continues from a fresh symbolic frontier constrained by the declared
  interface. Unchanged function parameters retain their entry identity.
- `observe(resource);`: project one view step from a held composite resource
  fact. This exposes immediate pure facts and viewed immediate contained
  resource facts without exposing owned contained permissions.
- `choose(k from requirement name);`: open a named existential precondition,
  introducing proof-local int32 value `k`.
- `choose(k from requirement N);`: the same operation by zero-based requirement
  index. Prefer labels for durable scripts.
- `witness(k = expression);`: prove the current existential goal by substituting
  the given int32 expression for binder `k`.
- `simp();`: request deterministic simplification when the proof block is
  checked.

The end of a `by { ... }` block checks the overall claim.

Explicit C branch execution composes with proof-level case analysis:

```click
if x >= 0 {
    execute_then_step();
    execute_step(); // Execute the first statement in the C then arm.
} else {
    execute_else_step();
    execute_step(); // Execute the first statement in the C else arm.
}
```

The branch steps execute only the selected control-flow edge. Ordinary
`execute_step()` calls handle statements inside the arm, so nested C `if`
statements can be entered with another explicit branch step.

Use `advance` when branch-local execution should establish a common interface
before the rest of the function proof:

```click
advance(statement(1).exit)
ensuring {
    fact y >= 0;
    owns buffer(data, len);
    views metadata(data, len);
}
by {
    if x >= 0 {
        execute_then_step();
        execute_step();
    } else {
        execute_else_step();
        execute_step();
    }
}
execute_step();
```

`statement(N).entry` means immediately before statement region `N` executes.
`statement(N).exit` means immediately after it completes. Lowering assigns
statement IDs globally in source preorder: a compound statement receives its
ID before the statements nested in its arms or body. A sequence itself does
not receive an ID. Every nested case must reach exactly the requested point
and establish every assertion. `advance` is the
execution-proof counterpart to `have`: `have` runs a pure proof without moving
the execution point, while `advance` proves a postcondition for a scoped code
region and advances to its exit. Facts and resources needed by the
continuation must be listed explicitly. Deterministic consequences of listed
resources, such as memory loadability and the view of an owned resource,
remain available.

Snapshots created inside the scoped execution are not exported. The function
entry state used by `old(...)` and the abstract target snapshot remain
available. Changed pointer-valued locals become fresh symbolic pointers at the
join. The interface must export the facts and resources needed to use them,
such as `views selected[0..len]`; symbolic pointers do not imply non-aliasing
with concrete allocations.

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
fact or resource fact required by the following `execute_step()`. Applications
after function exit remain path-local, so `result` and post-state expressions
are interpreted separately for each completed path.

Some successful `auto` proofs record replayable proof-step certificates when the
current proof-step language can express the argument.

An execution proof tracks an execution frontier: the current
execution point together with its enclosing continuation stack. Proof scripts can
start at function entry, advance by one statement with `execute_step();`, enter
a selected C branch, join branch-local proofs at an explicit statement point
with `advance`, pause at a statement
entry with `execute_until(statement(N));`, and execute to function exit with
`execute_rest();`. Resource steps such as `observe`, `unfold`, and `fold` can
happen between those execution steps.

The execution frontier carries the same global statement ID assigned by
lowering. The source layout uses that ID to identify branch children,
continuations, and nested loops. Checks inserted by annotation lowering remain
attached to their source statement and do not become extra proof steps.

Ordinary statement steps, explicit branch entry, and region execution-proof
traversal use the same certified condition and statement transitions. `advance` composes
those transitions inside its body and then replaces the reached branch-local
frontiers with the declared abstract interface. `execute_rest()` is the batch
form that continues from the same frontier to function exit.

`advance` accepts statement entry/exit targets and loop entry/exit targets. In
particular, `advance(loop_name.exit) ensuring { ... } by { ... }` executes to a
verified loop's abstract exit and makes the declared facts and resources the
only proof-visible interface afterward.

At function entry, `views composite(...)` resource requirements are projected
one step automatically, matching `observe(composite(...))` for immediate
contained views. Owned composite resources still require an explicit
`observe(...)` when a proof wants to read through the folded resource.

Existential proof steps are deterministic replay steps, not search tactics. A
typical existential-introduction proof names a witness:

```click
ensures found: (0..n).any(|k| { k == result }) by {
    symbolic_execute();
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
requires has_k: exists (int32 k) { k == x };
ensures again: exists (int32 j) { j == x } by {
    symbolic_execute();
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
    symbolic_execute();
    unfold(bytes_contains);
    choose(found from requirement has_x);
    witness(k = found);
    simp();
}
```

## Region Execution Proofs

Region proof blocks attach specifications and smaller execution proofs to code
regions:

```click
for statement(2) {
    assert i == 0 by auto;
}

for loop(0) {
    invariant i >= 0;
    invariant i <= n;
    mutable p[0..n] by frame;

    step {
        mutable p[i..i + 1] by frame;
    }
}
```

`statement(N)` selects the Nth source statement code region in structural
order. `loop(N)` selects the Nth `while` loop code region. A code region may
also be labeled with `as name`. Labels are the preferred proof-facing spelling
for execution targets and snapshots because they remain meaningful when nearby
source statements change:

```click
for statement(4) as update {
    assert y >= 0 by auto;
}

execute_until(update);
have at(update.entry, y) >= 0 by simp;
```

The same label can be used by `advance(update.exit)`, `at(update.entry, ...)`,
`at(update.exit, ...)`, and region tactics such as `frame(update)` when the
region kind is accepted. Numeric `statement(N)` and `loop(N)` references remain
the way labels are attached and are useful for short proofs.

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
```

The initial `loop_name.entry` support is available in invariants on that loop
and in its explicit `preserve` proof.

Statement entry and exit snapshots are currently recorded by deterministic
proof execution. `execute_step()`, `execute_until(...)`, and `execute_rest()`
record each deterministic boundary they cross. An `at(...)` expression reads
memory, reassigned parameters, and declared scalar, pointer, or array locals
from the selected state. Branch entries can have a unique snapshot. An explicit
loop `preserve` proof binds `at(loop_name.entry, ...)` to its fresh arbitrary
iteration state. Executing a verified loop records its unique abstract exit as
`at(loop_name.exit, ...)`. Historical iteration visits still require a future
selection model.

`assert` is a one-shot spec check at the selected statement code region. It
currently accepts the executable proposition fragment over current-state C
fragments.

`invariant` declarations generate obligations at loop program points. The
loop-level `initialize` proof establishes the complete invariant set before the
first iteration. The `preserve` proof assumes that set and the loop condition,
executes one body iteration, and reestablishes the set:

```click
for loop(0) {
    invariant 0 <= i and i <= n;
    invariant sorted(p, n);

    initialize by auto;
    preserve by {
        unfold(sorted);
        execute_step();
        simp();
    }
}
```

Either phase may be omitted, meaning `by auto`. An explicit preservation proof
runs in a fresh arbitrary-iteration context and must reach the loop back edge
on every proof branch. It can use ordinary proof steps, including `have`,
resource operations, proof-level `if`, and branch execution.

An explicit initialization proof is an ordinary pure proof at the actual loop
entry. It can use `apply`, nested `have`, proof-level `if`, `unfold`, and `simp`,
but it cannot execute C or transform resources. The loop-entry snapshot
`at(loop(N).entry, ...)` is bound while this proof runs. The facts it proves are
checked against the kernel invariant instances before rule construction.

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
either premise again. An omitted phase uses `auto` for that premise.

That abstract exit produces an opaque kernel `VerifiedLoopRule` over the
symbolic loop-entry state and its required assumptions. Subsequent function
claims must consume the registered rule when they encounter an annotated loop.
Additional assumptions are allowed, but an incompatible symbolic state or
missing rule makes verification fail; execution does not fall back to proving
the loop again.

## Loop Effects

Whole-loop effects:

```click
for loop(0) {
    mutable p[0..n] by frame;
}
```

Step-relative effects:

```click
for loop(0) {
    step {
        mutable p[i..i + 1] by frame;
    }
}
```

Whole-loop mutable segments must use stable names such as parameters. They
cannot depend on locals modified by the loop. Use `step` effects for
iteration-relative footprints.

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
- resource facts, when the failing proof step has a current resource context
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
