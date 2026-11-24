# Loops and invariants

This page explains how Click proves C loops: invariants, termination measures,
loops over memory, and the loop proof tactics.

A loop that no contract-admitted path reaches needs no ranking measure. Exact
checked execution retains this fact even when ownership adds an inherited
frame check to the source loop; reachable summarized loops still require their
own termination evidence (`mdtests/unreachable_owned_loops_terminate.md`).

Loops require summaries. Click cannot prove a symbolic loop by unrolling it
forever.

When a sidecar is parsed against its C or Rust source, an unbound value name
in a loop specification is a type error naming the clause. This includes
invariants, decreases, resources, and initialize and maintain proofs; C locals and
lexically scoped proof binders remain valid names
(`mdtests/loop_unknown_name_in_invariant.md`).

A loop invariant is a fact that must hold:

- before the first iteration,
- at the start of every iteration,
- and after one iteration preserves it.

A loop's `views` clause and `viewable` invariant over a local pointer use its
declared element type:
`uint8*` counts bytes and `uint64*` counts eight-byte elements. The C and typed
Rust annotation paths retain those types; the invariant does not acquire
read authority merely from the pointer declaration.

A nested loop can select a subview through an outer cursor whose address is
proved equal to that subrange of the enclosing view. Resource selection uses
the checked pointer-alias graph and range bounds at entry, retaining the
enclosing owner's authority and any stable-view binding. A pure `viewable`
fact alone supplies no resource.

A loop may declare conditional resources using the same `if` form as a
resource body:

<!-- verified-example: mdtests/mutex_parity_direct.md -->
```click
loop {
    decreases n - i;
    invariant 0 <= i and i <= n;
    if i % 2 == 1 {
        owns mutex_guard(&object->mutex);
    }
    owns mutex_live(&object->mutex);
    owns object->mutex;
}
```

The condition is evaluated at entry, at an arbitrary iteration's start, and
at each backedge. Write the condition as a scalar comparison over C values,
independent of the mutex heldness it describes. When it is true, the loop
must own the stated resource.
A branch proving the condition may use that ownership; proving the condition
alone does not create ownership. The next iteration may carry a different
mutex acquisition, but it must belong to the same initialization.

An ordinary named resource with a conditional `owns` body remains an
alternative when the abstraction is useful elsewhere. The direct form needs
no extra model field or explicit folding and unfolding.

The current symbolic case supports guards of empty mutexes with locally owned
lifetimes. Other conditional `owns` and `views` clauses require their condition
to be decided when the loop resource context is formed. Conditional named
binders and nested conditional blocks are not supported yet.

These checks prove that every finite iteration prefix is safe and that the
invariant is available if the loop exits. They say nothing about whether the
loop exits, so a summarized loop also declares why it ends: every `loop`
block carries either a `decreases` clause or the `diverges` marker. A
constant-true service loop writes `loop diverges { ... }` and can still have a
useful invariant even though it has no exit state.

The `decreases` clause is one expression, and what it names decides
which measure it is: a nonempty int32, unsigned, or `Integer` ranking
expression, a lexicographic
tuple of them, or one of the loop's own resource binders. The same uniform
rule applies to a C function's own `decreases`; there is no `decreases
resource` form anywhere.

<!-- verified-example: mdtests/count_to_n_loop_invariant.md -->
```click
loop {
    decreases n - i;
    invariant i >= 0 and i <= n;
}
```

<!-- verified-example: mdtests/c_decreases_lexicographic_loop.md -->
```click
loop {
    decreases (i, j);
    invariant i >= 0;
    invariant j >= 0;
    invariant j <= 2;
    ...
}
```

The expression is checked at each continuing body path: the loop guard and
the available function preconditions and invariants must establish that every
component is nonnegative. A tuple decreases lexicographically: an earlier
component must remain equal and a later component must be strictly smaller at
some pivot. This supports count-up loops as well as countdowns, for example
`decreases limit - index;` when the body increments `index`. A component need
not be a C expression: it is any pure ranking expression, including a memory
read, an application of a pure Click function, or a resource model field, and
Click reads the one declared component at the iteration's entry and again at
the back edge, exactly as it reads an invariant about the same cells. It may
not mention `old` or `at`, because a measure that names a fixed state reads
the same state twice and so can never decrease. A loop measure cannot read a
C local if the program takes its address. A write through a pointer could
change that local outside the updates the ranking check tracks.
Each component is checked in its own type, so its arithmetic must also be
defined under those assumptions. This produces separate termination evidence; it does not
change what an invariant or a postcondition means. A separately ranked nested loop is
treated as a terminating phase when checking its enclosing loop; an outer
ranking variable that phase writes takes an unknown value on the way out,
because the inner loop's final state is not reconstructed here. The enclosing
loop's invariants, which its rule certifies at the back edge as well as at the
head, are what must bound the resulting ranking components and establish the
decrease.
When a loop contains a numeric recursive call, the loop and the recursive edge
need separate evidence: the loop must have its own ranking, and the
function-level `decreases` measure must strictly decrease at every recursive
edge. The loop guard is used when proving the recursive argument is
nonnegative. The numeric function-level measure must remain unchanged by the
loop body; a call whose descent depends on the loop's changing counters is
ranked instead by a function-level expression or tuple measure, discharged
from the loop invariants. A read-only structural-resource call inside a
ranked loop is supported when the parent resource is observed before the loop;
the call must still receive a direct contained child. Pointer-valued branch guards are not scalar
ranking facts, so the ranking checker checks the scalar measure on every path
without importing those pointer comparisons. A recursive call that consumes a
child inside a ranked loop is ranked by a model measure, and the loop may free
the node and continue
(`mdtests/c_decreases_model_measure_recursion_consumes_inside_loop.md`).

Termination is also a claim about everything the loop body calls: every
reachable loop, recursive cycle, and callee needs a checked ranking proof. A
callee with a contract answers with a verified rule of its own, and an
`extern` contract is trusted to return exactly as its `ensures` is trusted. A
header-provided `static inline` helper with a contract is such a callee. One
with no contract has no call boundary, since its body executes at the call
site, so it is read as a node of the caller's own call graph instead. A
contract-less helper whose body is straight-line, with no loop, no recursion,
and no call to anything not itself terminating, terminates by construction,
so a ranked loop may call one:
`mdtests/c_decreases_loop_inline_helper.md`, and the rbtree ascent of
`mdtests/rb_ascending_walk_to_root.md`, which climbs through the unchanged
Linux `rb_parent` under `decreases c;`. A contract-less helper carrying a
loop still needs that loop ranked and certified, and a recursive one is a
cycle needing a checked rule; both are refused otherwise
(`mdtests/c_decreases_rejects_inline_helper_loop.md` and
`mdtests/c_decreases_rejects_recursive_inline_helper.md`). A helper's own
ranked loop is planned under the translation-unit-qualified name its body
executes under rather than the ordinary name its sidecar contract uses,
which is what lets the plan reach the function the call site names
(`mdtests/inline_helper_ranked_loop.md`).

The [`perpetual-service`](https://github.com/clicklang/click/tree/master/examples/perpetual-service) example
combines a `diverges` contract with an opaque verified call and a composite
resource transferred through every iteration.

An execution proof has a frontier: the boundary between C that has already
been checked and C that remains. `loop { ... }` handles the C loop exactly at
that frontier. It does not name a loop by source-order number and does not jump
forward to find one. If the frontier is not at a loop, the tactic fails.

The tactic checks initialization and one arbitrary iteration, constructs a
kernel-checked loop rule, applies that rule once, and advances the enclosing
frontier to the loop exit. Since the C can reach a loop head more than once, the
preservation proof is about one arbitrary iteration rather than one concrete
iteration; the proof path reaches the head once.

That frontier does not have to be the top level of the script. A C loop
guarded by an `if` is reached on one path only, and the proof reaches it by
splitting the `if` first: `loop { ... }` is then written in the arm whose
frontier is at the loop. Both conditional forms take it. A `branch` arm
runs the loop rule and joins its sibling at the statement after the `if`,
which needs an `ensuring` interface whenever the arms leave the loop's locals
in different states — the summarizing arm holds the loop's abstract exit while
the other still holds what it had (`mdtests/loop_inside_a_branch_arm.md`,
`mdtests/loop_inside_a_branch_else_arm.md`). A proof-level `if` arm runs the
loop rule and then continues to its own function exit, since those arms never
join (`mdtests/loop_inside_a_proof_if_arm.md`). Either way the invariants are
established from the arm's own state, with the arm's path condition available
as a premise, and the arm owes the whole bundle: a `decreases` the enclosing
function's termination judgment still requires, and an invariant the body does
not preserve is refused exactly as at the top level
(`mdtests/loop_inside_a_branch_arm_rejects_a_false_invariant.md`). The
implicit tail is not an alternative here: it reaches the guarded loop and
stops, because the loop condition has two feasible paths and the tail invents
no invariants. `step_until` stops sooner, at the `if` it never splits.

A labeled loop can also expose its entry point to the invariant:

<!-- verified-example: mdtests/loop_entry_program_point.md -->
```click
loop drain {
    decreases n;
    invariant n >= 0;
    invariant n <= at(drain.entry, n);
    ...
}
```

Here `at(drain.entry, n)` means the value of `n` at the loop's entry point,
just before the loop region starts.

For a simple counter loop:

<!-- verified-example: mdtests/count_to_loop_initialize_by_solve_and_preserve.md -->
```c
int32 count_to(int32 n) {
    int32 i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

the proof first advances through the statements before the loop, then declares
the bounds on `i` at the frontier:

<!-- verified-example: mdtests/c_decreases_count_up.md -->
```click
by {
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0;
        invariant i <= n;
    }
    step();
}
```

The full induction syntax names its two obligations explicitly:

<!-- verified-example: mdtests/count_to_loop_initialize_by_solve_and_preserve.md -->
```click
loop {
    decreases n - i;
    invariant i >= 0;
    invariant i <= n;

    initialize by close();
    maintain by {
        step();
        close();
    }
}
```

`initialize` is a pure proof of all invariants at the actual loop entry. Its
script may use exactly `unfold(predicate(args))`, `apply(theorem(args))`, `have`,
`close()`, `normalize()`, `rewrite(...)`, `all`, `cases`, and
proof-level `if`;
anything else is rejected with `` `initialize` is a pure proof and cannot use
`<tactic>` ``. `maintain` assumes all invariants and the loop condition,
executes one complete body iteration, and proves all invariants again. Either
proof may be omitted; bounded automation owned by the `loop` keyword supplies
an omitted phase. Expanding that keyword writes all omitted phases explicitly.

An omitted `maintain` walks the body as a function's implicit tail walks a
function. At a C `if` whose condition the path does not decide, it splits, and
each arm runs on as its own path to the back edge, a `break`, a `continue` or
a `return`, where it closes the invariants with everything it established
(`mdtests/an_automatically_closed_loop_splits_at_its_c_branches.md`,
`mdtests/an_automatically_closed_loop_closes_each_branch_arm.md`). Sequential
`if`s multiply its paths. The loop closer shares the implicit tail's step
budget and limit of 1,024 splits, and it can also reach its deterministic
work limit while checking those paths
(`mdtests/a_branching_loop_stops_at_the_work_limit.md`). `branch ensuring { ...
}` joins an `if`'s arms and states what both establish, so the rest of the
body is checked once
(`mdtests/a_written_branch_interface_carries_what_an_invariant_needs.md`).
An interface fact holds in an arm only together with what its terms need to
denote a value, so an arm that proves `p[j] <= p[j + 1]` for the interface
also proves `defined(j + 1)`
(`mdtests/bubble_pass3_max_suffix.md`,
`mdtests/an_interface_fact_needs_its_terms_defined_in_each_arm.md`).
Two kinds of `if` keep their arms as separate paths: one with an arm that
leaves another way (a `break`, a `continue`, a `return`), and the body's last
statement, which has nothing after it to walk twice.

An invariant's side conditions are invariant content. These are what its
terms need to denote a value: that `i + 1` does not overflow in
`to_integer(i + 1)`, that an integer converted back to `int32` fits, or the
span half of a stated range (see [Viewable ranges](viewability.md)). The
head, the body and the exit assume them with the invariant, so the entry and
every back edge owe them: each is an entry goal of its own beside the
invariant's body, proved by that invariant's proof, and a member of the
back-edge bundle. An entry that cannot establish one is refused by naming it,
as in ``loop 0 invariant 1 entry, owing `defined((i + 1))` ``.

## How an `initialize` script divides up

Each invariant gets its own entry goal, so an `initialize by { ... }` script is
read as three parts, in this order:

- a leading run of `unfold(predicate(args))` and `have` steps that name something
  other than an invariant. These are *helpers*: each is proved once, where it
  is written, and its fact is available to everything below it.
- one `have` per declared invariant, in declaration order, naming the
  invariant exactly as the `loop` head writes it. Such a `have` is that
  invariant's own proof, and no other invariant reads it.
- an optional trailing `close()`.

A script that does not name the invariants individually — `initialize by
close();`, or a helper prefix followed by `close()` — is one shared proof: every
invariant's entry goal is proved by the same remaining steps, with the helper
facts already available.

That division is what expansion prints. A smart tactic inside an invariant's
own `have` expands to the same `have` with a checked body, left where it was
written; a trailing `close()` that stands for the rest of the phase expands to
one `have` per invariant, and the helpers above it are not copied into them. A
`close()` written after the invariants are already named contributes nothing,
so expanding it removes it. `maintain by close();` is the same whole-phase shape
one phase over, and expands to the planned preservation proof.

## What invariants do

An invariant is the bridge from the loop body to the postcondition. If the
postcondition needs `i == n` after the loop, Click must know enough at loop exit
to combine:

- the invariant facts,
- the failed loop condition,
- and the function requirements.

The failed condition describes an exit *if one occurs*. Invariant preservation
does not prove that such an iteration is eventually reached. The loop's
`decreases` clause certifies that it is; only a loop or function marked
`diverges` goes without that evidence.

### The pass count

`iterations` names the passes a loop has completed, as a mathematical
`Integer`. It is in scope in the loop's `invariant` clauses and its
`initialize` and `maintain` proofs, so an invariant can state a local over it
instead of over another counter:

<!-- verified-example: mdtests/a_loop_pass_count_names_the_passes_after_the_loop.md -->
```click
loop {
    decreases n - i;
    invariant 0 <= i and i <= n;
    invariant i == iterations;
    invariant total == 2 * iterations;
}
```

The loop rule binds it per phase: the entry checks the invariants at `0`, the
head assumes them at a fresh `K` with `0 <= K`, and the back edge checks them
at `K + 1`. A `decreases` component reads it the same way, at `K` and
`K + 1`, so `decreases n - iterations` ranks the loop. A `continue` is a back edge; a `break` exits during a pass that
does not count, so the exit's count is the head's `K`. Past the loop the proof
names that `K` as `loop(i).iterations`, the count the exit facts are stated
over (`have loop(0).iterations == n`). A nested loop's `iterations` is its own
count. The checked examples are listed under
[Loop transitions](../reference/tactics/index.md#loop-transitions).

### Short-circuit guards

A guard with `&&` or `||` leaves the loop by one path per operand that can end
it. `while (a != 0 && p[0] != 0)` exits when `a` is zero, and also when `a` is
nonzero and `p[0]` is zero; the second path never evaluates the first operand
away. Every one of those paths reaches the same exit state, so the loop rule
certifies them together and the exit states their join: everything they all
state — which includes every invariant — plus the disjunction of what each
states alone, here `a == 0 or p[0] == 0`. A proof that needs to know which
operand failed splits on that disjunction with `cases`:

<!-- verified-example: mdtests/loop_conjunctive_guard_exit_join.md -->
```click
have p[0] == 0 by {
    cases {
        a == 0 => {
            contradiction(a == 0);
        }
        p[0] == 0 => {
            close();
        }
    }
}
```

The negation of the first operand alone is *not* assumed at the exit: the loop
really can stop with `a` nonzero. An operand the function has no authority to
read leaves the guard undecided rather than dropping its path, and the loop is
refused — but an operand is read under the truth of the operands before it, so
a conjunct that refutes an arm of a folded modeled instance can give the next
conjunct the authority to read through it. That is the arm selection described
under [structural loop measures](#structural-loop-measures).

A `||` guard is the mirror image, and joins the same way on the way *in*.
`while (a > 0 || b > 0)` has one way out and one way in per operand that can
start an iteration, and the body is proved once against every entry path. So
the entry paths export their join too: everything they all state, plus the
disjunction of what each one states alone, here `a > 0 or b > 0`, in the
guard's short-circuit order rather than the order the paths were enumerated.
Each entry path checks the written `maintain` body under its own guard facts.
Its tactics may produce different certificates on different paths; retained
proofs and expansions keep those certificates under the corresponding entry
guards. A proof can also use `cases` over the common entry disjunction:

<!-- verified-example: mdtests/loop_disjunctive_guard_entry_join.md -->
```click
have 0 < to_integer(a + b) by {
    cases {
        a > 0 => {
            close() using { a > 0; b >= 0; a <= 1; b <= 1; };
        }
        b > 0 => {
            close() using { b > 0; a >= 0; a <= 1; b <= 1; };
        }
    }
}
```

As at the exit, the first disjunct alone is not assumed: the loop really is
entered with `a` zero and `b` nonzero, and a `maintain` body that cites the
first operand's fact on its own is refused
(`mdtests/loop_disjunctive_guard_entry_join_is_a_disjunction.md`).

### `break`, `continue`, and `return` in the body

One certified iteration is a path that reaches the body's end, a `continue`, or
a `break`, or that returns from the function. A path that stops anywhere else
has not been proved and the loop is refused — but a body that merely is not
written yet is refused with a *report* of where it got to rather than with the
bare rule; see
[the frontier of an unfinished `maintain`](#the-frontier-of-an-unfinished-maintain).

A `continue` transfers to the loop's shared continuation: a C `for` runs its
update, and a `do ... while` reaches its post-test, including any calls in that
test. Body scopes end before either region runs. The invariant and measure
are owed only when that continuation actually reaches the back edge; a false
post-test exits the loop instead. The update and test each have one source
region, including when a continue comes from inside a switch.

A `continue` reaches the back edge through that continuation. Everything the
body's end owes is owed there: the loop's binders are bound again on the state
after the continuation, the invariants are closed there by `close()`, and a
declared measure must have descended there.

<!-- verified-example: mdtests/loop_body_continue_back_edge.md -->
```click
maintain by {
    step();
    step();
}
```

A `break` is an *exit*. The invariants are not closed on it — a `break` leaves
the loop with whatever that path established — and no measure is required to
decrease on it. Its facts join the guard-false exit and the other `break`
exits into the loop's single successor, on the same terms as the exits of a
short-circuit guard: everything the exits all state, plus the disjunction of
what each states alone. A `while (true)` has no guard-false exit, so its
successor is the join of its `break` exits alone, and a claim after the loop
reads that disjunction
(`mdtests/loop_body_break_exit.md`). Dropping a `break` path
instead would prove claims the C never reaches, which is why `result == 0` is
refused for a loop that can break out with the guard still true
(`mdtests/loop_body_break_exit_claim_rejected.md`).

Both work inside a proof `if` and a proof `match` arm
(`mdtests/loop_body_break_in_match_arm.md`), which is how a body's `if (...)
break;` is written: those arms are never joined, so each path reaches the loop
rule on its own. A `branch` is the joining form and has nothing to join when
one arm leaves the loop, so it refuses and names the proof-level form
(`mdtests/loop_body_break_in_branch_arm_rejected.md`).

A `return` is terminal for the whole function. It owes neither the loop's
invariant and ranking bundle nor a join with the loop's ordinary successor.
Write a returning C branch as a proof-level `if`: the returning arm stops at
function exit, while every continuing arm independently reaches the back edge
and closes the bundle
(`mdtests/a_return_inside_an_explicitly_preserved_loop_body_is_a_function_exit.md`).
Omitted preservation uses the same per-path rule
(`mdtests/a_summarized_loop_body_return_is_certified_with_its_value.md`). The returning path is a
function-exit path of the enclosing proof: the loop rule exports it as a
`return` outcome with the value and state the body returned in, so the
postcondition and the resource obligations are checked on it exactly as on a
`return` after the loop
(`mdtests/a_return_inside_a_summarized_loop_body_is_a_function_exit.md`), and
a natural cycle whose only exit is a `return` is certified on that exit rather
than vacuously
(`mdtests/a_natural_goto_cycle_return_exit_is_a_function_exit.md`). A checked
forward `goto` out of a natural cycle similarly exports its target and exit
state. Execution resumes at the label, where returns, postconditions, and
undefined behavior are checked. The implicit tail after `loop` runs the code at
that label and closes the contract, so the script needs nothing after `loop`
unless the label's code needs proof work of its own. Several checked edges to the same label retain
the disjunction of their exit facts rather than discarding an edge
(`mdtests/natural_goto_forward_exit_state.md` and
`mdtests/natural_goto_forward_exit_multiple_edges_state.md`). A natural
cycle with both terminal returns and continuing forward goto paths closes
each returned outcome in its preservation arm; expansion retains those
arm-local closers (`mdtests/natural_goto_forward_exit_and_return.md`). When
exit edges assign different local values, the join also exports a disjunction
of equations for the successor values. This lets the proof name the possible
values without naming forgotten loop-iteration guards
(`mdtests/natural_goto_forward_exit_differing_states.md`).

### `do ... while`

A `do ... while` reads its guard after the body, so the state a body path ends
in *is* its guard-false exit; there is no exit at the head. That state is
always one of the loop's exits, and it joins the `break` exits into the single
successor exactly as a `while` loop's guard-false exit does
(`mdtests/do_while_break_exit_join.md`). Without it the loop exported no exit
at all and every claim after it held vacuously, which is why both
`mdtests/do_while_break_exit_vacuous_rejected.md` and
`mdtests/do_while_no_exit_state_rejected.md` are negatives.

### Exits that reach different states

A `break` that assigns or stores before leaving stands at a different state
than the guard-false exit and than the other `break`s. The loop still has one
successor, and it is described the way the loop head describes an arbitrary
iteration — the rule of [modeled instances in
loops](#modeled-instances-in-loops), applied at the exits:

- the loop's declared binders are bound again at each exit by family and
  argument equality, whatever the body called them, and a binder no exit can
  hand back is a refusal naming that binder and that exit
  (`mdtests/loop_break_exit_missing_binder_rejected.md`);
- every component the exits disagree about becomes one fresh name — a binder's
  model or arguments, a local, a cell one exit wrote differently;
- each exit contributes, as its own disjunct, what it established about those
  fresh names, so the successor states exactly "this is what one of the exits
  reached" and nothing more.

A binder argument declared as a current local, such as `owns c: cursor(cur,
anchor);`, shares that local's joined value when every exit holds the instance
at its own `cur`. Rebinding can use pointer equalities established on that
particular exit (`mdtests/loop_exit_resource_argument_uses_exit_alias.md`);
other exits cannot supply missing equalities
(`mdtests/loop_exit_resource_argument_requires_exit_alias.md`). A helper after the loop can therefore consume `cursor(cur,
anchor)` even if the exits chose different cursors
(`mdtests/loop_exit_resource_argument_tracks_current_local.md`). This does not
preserve the entry pointer or equate unrelated model fields
(`mdtests/loop_exit_resource_argument_rejects_entry_pointer.md`).

A cell the exits wrote differently is a cell folded into one of the declared
binders, since the body owns nothing else, and a proof after the loop reads it
back through that binder's model. A loop that declares no binder has nothing to
read such a cell through, and the difference is refused naming the cell
(`mdtests/loop_break_exit_unowned_cell_rejected.md`).

The exits are compared by what they hold, not by how they came to hold it. An
exit that unfolded and refolded a binder and an exit that left it untouched
hold the same instance, whatever order their folds ran in
(`mdtests/loop_break_exit_join_ignores_fold_order.md`), and a cell only some
exit read, because only that path opened the instance owning it, is knowledge
the successor does not claim rather than a difference between the exits
(`mdtests/loop_break_exit_join_sets_aside_unshared_cells.md`).

Two layouts of one state are one state. Memory is compared by its cells, the
same pointers with the same values, whether the cell cache holds one as a
written cell or as a slot of the run an `unfold` seeded
(`mdtests/loop_break_exit_join_compares_cells_not_their_cache.md`). Resources
are compared after the merges the resource algebra itself defines, so a view
of a cell that one exit holds twice, because it opened the binder and folded
it back, is the view the other exit holds once
(`mdtests/loop_break_exit_join_refolded_and_untouched_binder.md`). Nothing
else is looked through: a block, a read-only status, a heap lifetime, or an
owned or lent resource still has to agree
(`mdtests/loop_break_exit_differing_ownership_rejected.md`).

A contracted call may return a cell as a checked load equation rather than
a cached store. When every exit proves the same exact integer or pointer
value, the join retains that value, including a call on one exit and a direct
store on another (`mdtests/loop_break_exit_contract_call_joins_a_direct_store.md`).
An owner's own observation and identity expansion cache do not add authority;
borrow-bound views and nontrivial resource descriptions still have to agree.
Different stored values remain a named join refusal
(`mdtests/loop_break_exit_contract_call_different_store_rejected.md`). Numerical
floating equality and `bool` reads (the `Bool` `byte != 0`) do not establish
identical stored bits and are not used to fill the cell cache.

Exits can also disagree about bookkeeping no C expression observes after the
loop, and the join reconciles each piece in the direction that claims less:

- A value-only binding written inside the loop but absent at its head is
  discarded when some exits never produce it. This covers result temporaries
  created by lowering calls in conditions
  (`mdtests/loop_call_condition_temporary_exit.md`). It supplies no value for
  a later read, and leaves declared objects, memory, and ownership checked.
- A local some exits have initialized and others have not stays declared,
  with its slot and type, but uninitialized. A read of it after the loop is
  refused (`mdtests/loop_break_exit_uninitialized_at_one_exit_is_not_read.md`);
  that read is what this gives up.
- A path that called a function with a local records that the local's block
  has ended. The successor keeps every exit's record, so a pointer that may
  designate such a block is not readable through
  (`mdtests/loop_break_exit_stale_alias_after_join_is_not_read.md`).
- The counter that names re-entered declarations takes the largest value any
  exit reached, so no ended block's identity is issued again.
- When the exits' memories disagree on what they have forgotten or on their
  contract-call state epochs, the
  successor's memory keeps the cells every exit holds and takes a freshly
  minted identity with no recorded history
  (`mdtests/loop_break_exit_after_a_call_with_a_local_joins.md`). A load after
  the loop of a cell the successor does not hold is then related to no load
  before or inside the loop; that relation is what this gives up. Cells every
  exit holds keep their values
  (`mdtests/loop_break_exit_after_a_call_keeps_cells_every_exit_holds.md`),
  and a loop whose exits agree keeps its memory's identity and every read
  equality through it (`mdtests/loop_break_exit_ordinary_join_keeps_post_loop_read.md`).

What every exit states survives the join as an ordinary fact, so a claim that
does not distinguish the exits needs nothing special
(`mdtests/loop_break_exit_refold_join.md`).

That includes a fact each exit states about its own value for a binder the
join renamed. The join restates every exit's facts with that exit's value,
as a term, replaced by the successor's name: an exit that holds `x` at
`Cell::Missing` and states `Cell::Missing == old(x.model)`, and one that holds
it at `Cell::Red(identity)` and states `Cell::Red(identity) == old(x.model)`,
both restate `x.model == old(x.model)` about the successor. On each exit's
path the name equals that exit's value, so the restated fact holds on that
path, and a fact every exit restates identically holds whichever exit was
taken. It is kept as an ordinary fact
(`mdtests/loop_break_exit_keeps_a_fact_every_exit_restates.md`). Nothing is
searched for or proved again: a fact one exit does not state is not kept
(`mdtests/loop_break_exit_fact_one_exit_does_not_state_is_dropped.md`), and a
fact about another binder is not restated about the renamed one
(`mdtests/loop_break_exit_fact_about_another_binder_is_not_restated.md`).
Identity is of the kernel's propositions, so two exits whose facts about
their own arm bindings print alike state different facts, and neither is
kept. A claim that does distinguish them
is read off the exported disjunction with `cases`. The disjunct also uses
the successor's model name inside pure getters, so a fact such as
`pending(x.model) == 0` does not require naming an instance left inside
the loop (`mdtests/loop_exit_restates_model_getters.md`):

<!-- verified-example: mdtests/loop_break_exit_binder_model_join.md -->
```click
have c.color == Color::Red or c.color == Color::Black;
```

That is a `while (true)` whose two `break`s paint the node a different colour
and refold the binder before leaving. Each exit proves the colour disjunction
for the instance it holds. The successor can use that same fact with its
rebound `c`. A local the exits disagree on works the same way
(`mdtests/loop_body_break_exit_joined_state.md`), and a claim only one exit
supports still fails
(`mdtests/loop_body_break_exit_joined_state_rejected.md`).

A guard-false exit stands at the loop head, where the locals the body writes
are fresh names of their own. Its own facts are therefore restated about the
successor's names before they are disjoined — valid because that exit's own
disjunct is the equation saying the two are the same value — so the disjunction
speaks in names a proof after the loop can write. A `break` exit's facts about
the *head's* values are left as they are; they are true, but a proof after the
loop cannot name what they are about, so a `cases` over such a disjunction is
out of reach.


When exit states cannot form a common successor, the diagnostic names the
components that still differ after the loop's permitted abstractions. It
reports changed local bindings, memory, resource ownership, call bindings,
authority ledgers, population effects, or automatic-storage bookkeeping.
Counters and flags show both compared values; call bindings show entry counts.
Local names are capped at twelve, with an omitted count. These details explain
the rejected comparison and do not relax the join rule.

## Memory loops

Pointer-writing loops often need both arithmetic invariants and memory facts:

<!-- verified-example: mdtests/loop_owns_preserves_symbolic_index.md -->
```click
loop {
    owns p[0..n];
    invariant i >= 0;
    invariant i <= n;
}
```

The arithmetic invariants prove access bounds. The loop's owned resources
summarize what memory the loop may write; with no clause of its own it may
write exactly what the function owns.

A loop that declares a resource havocs all memory the resource owns, so the
cells such a loop never writes keep their values only through a frame
invariant, for example
`forall (k: int32) { 0 <= k and k < start implies arena->occupied[k] == old(arena->occupied[k]) }`.
`old(...)` means the function's entry state here exactly as it does in the
loop's proof bodies, so a body can restate or instantiate the clause as
written. The map may be reached through a struct field the loop does not
write: the field's cell stays with the enclosing frame, the loop head keeps
its value, and every read of `arena->occupied` names the one pointer loaded
at entry, so the frame closes at the back edge
(`mdtests/loop_frame_keeps_two_header_cells_of_a_field_map.md`, which frames
individual cells of `arena->occupied`). A loop
that writes the field loses the frame
(`mdtests/loop_frame_rejects_rewritten_base_field.md`).

The field may also belong to a field-bearing resource the proof unfolds
before the loop, as `examples/arena`'s `arena_state` owns `&arena->occupied`.
Unfolding names each pointer field cell as the word that carries its load,
and a clause's read of that cell is the load it names, so the field itself
adds no member to the bundle; only the map cells do, one or two hops away
(`mdtests/loop_frame_keeps_a_two_hop_map_beside_a_written_array.md` frames a
map two field hops from its descriptor). `old(...)` in a loop written inside
the proof reads the checked function entry even when the proof unfolded a
resource before its first step
(`mdtests/loop_invariant_old_model_when_the_unfold_precedes_execution.md`).
A map that is viewable at the function entry only inside a folded resource
is framed against the loop entry instead, `arena->occupied[k] ==
at(mark.entry, arena->occupied[k])`, with its viewability stated just before the loop so the
loop-entry member has a premise to cite (`examples/arena`'s `arena_free`
frames its `clear_occupied` loop this way).

A loop that declares a resource havocs what the resource may own, and an
iterated clause counts every element it could hold, so the footprint can
cover memory the loop never holds. A cell the function keeps owning outside
the loop's declarations is kept at the head anyway: the body sees it only as
a view and cannot store to it
(`mdtests/loop_body_cannot_write_function_owned_cells.md`). A descriptor the C
condition reads therefore reads the same value at every iteration, as
`region->end` does in `examples/arena`'s `arena_free`, whose loop owns a
clearing window with iterated ownership of `data`.

## Modeled instances in loops

A loop header can also name a resource instance, with the binder syntax a
contract uses:

<!-- verified-example: mdtests/loop_binder_counter_model.md -->
```click
loop {
    owns c: counter(p);
    invariant c.count == old(c.count) + i;
}
```

The loop then behaves like a callee contract for that instance. At the loop
head it consumes the enclosing owned instance whose family and arguments
match, and binds `c` to it for the body. Exactly one instance must match; two
matching instances are an ambiguity the loop refuses rather than resolves, and
none is an error. An instance the loop does not declare stays with the
enclosing frame: the body can neither read nor write through it, and it is
returned after the loop.

The head is an arbitrary iteration, so the model `c` carries there is arbitrary
too. Only the invariants say anything about it, and `old(c.count)` still means
the function-entry model of the function's own binder of that name. There is
no loop-entry read of a model.

The body holds `c` and works with the ordinary proof operations. Here one
iteration first states the model the invariants give the head's arbitrary
instance, `c.count == i`, which bounds the cell the increment writes; it then
opens the instance, writes the cell it owns, and folds it again with the model
that write produced:

<!-- verified-example: mdtests/loop_binder_counter_model.md -->
```c
void bump_n(struct cell* p, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        p->value = p->value + 1;
        i = i + 1;
    }
}
```

<!-- verified-example: mdtests/loop_binder_counter_model_concise_proof.md -->
```click
resource counter(p: struct cell*) {
    field count: int32;
    owns p->value;
    fact p->value == count;
}

void bump_n(struct cell* p, int32 n) {
    requires n >= 0;
    requires n <= 1000;
    owns c: counter(p);
    requires c.count == 0;
    ensures c.count == old(c.count) + n;
} by {
    step();
    step();
    loop {
        decreases n - i;
        owns c: counter(p);
        invariant i >= 0;
        invariant i <= n;
        invariant c.count == old(c.count) + i;

        initialize by close();
        maintain by {
            have c.count == i by { close() using { c.count == old(c.count) + i; old(c.count) == 0; }; }
            unfold(c);
            step();
            step();
            let c = fold(counter(p), { count: old(c.count) + i });
        }
    }
    have i == n by close();
}
```

The binder's arguments are read where they are used. The head builds the
binder's instance at the loop's own havocked values, so a cursor the body
reassigns is already the head's cursor, and the back edge reads the
clause again in the state the body reached. That is what lets a body hand a
child to the next iteration: after `root = root->left`, an
`owns sub: tree_at(root);` binder names the subtree at the new cursor by
proved argument equality.

The back edge selects the instance the same way the head did, with the
arguments read in the current state, and binds the loop's name to it whatever
the body called it. A body that folds its result as `let d = fold(counter(p),
...)` still hands `c` back, because `d` is the owned `counter(p)`. A body that
ends without an instance at those arguments fails at the back edge, named.
The ownership join compares the binder's family and arguments and leaves its
model to the invariants, which is what lets an iteration change the model at
all.

After the loop, the name denotes the final instance, with the invariants and
the negated guard available; above, `i == n` turns the invariant into the
postcondition. A loop binder may reuse an enclosing binder's name, as `c` does
here; that is a rebinding of the same instance rather than a second one.

Reuse the enclosing name. A fresh name takes the instance over for the rest of
the function, so it names nothing before the loop, and an invariant that reads
it at loop entry has nothing to read. That is refused by name rather than as a
failed lowering (`mdtests/loop_binder_rejects_fresh_name_in_invariant.md`).

### Structural loop measures

A loop that walks a recursive structure has no numeric counter to rank, and
the structure itself is the witness. Such a loop names its binder: a loop that
declares `owns sub: tree_at(cur);` writes `decreases sub;` beside its
invariants.

The rule at the back edge is that the instance the binder ends holding must be
a strict contained descendant, in the exact resource definitions, of the
instance it held at the loop head, carrying the submodel that child names. A
model is a finite inductive term, so a strictly deeper submodel at every back
edge is well-founded. No counter, size function, or automatic unfolding takes
part, and a descending loop decreases its subtree binder while an ascending one
decreases its context binder, because a rotation may grow the focused subtree
while the context strictly loses a frame.

A direct child is one step of that descent, and it is not the only step a body
takes. The uncle-red case of the Linux insert fixup recolours the parent and
the uncle, sets `node = gparent`, and goes round again, so the frame the next
iteration starts at is two above the one this iteration started at. The measure
follows the body down as far as the body opened: each step needs a premise
naming that instance's constructor, and the only thing that produces one is the
body unfolding the instance, so the descent walks the unfold evidence the proof
already left behind and stops at the first instance nobody opened. It is a walk
over the constructors the path made explicit, not a search for one, and a back
edge that hands back an instance the body never reached that way is refused by
name (`mdtests/loop_decreases_strict_descendant.md` is the two-step positive).

Which arm names the children is decided by the loop's invariants, playing the
part of a contract's requirements. That is the same arm selection contract
lowering performs, so the measure needs a `match model` resource whose
constructor the invariants pin down; a binder whose constructor they leave
open is refused by name rather than guessed. The invariants also publish the
selected arm's cells as read authority at the loop head, which is what lets a
guard such as `root->left != 0` read through the focused subtree the binder
holds.

A guard's own earlier conjuncts count as premises for the conjunct after them.
A short-circuit conjunct is read under the truth of the ones before it, so a
prefix that refutes an arm publishes what the arms it leaves possible agree on,
and the next conjunct may read what the prefix unlocked. The `rb_next` ascent
`while (parent != 0 && node == parent->rb_right)` is the shape: no arm of a
three-constructor frame is selected at the head, `parent != 0` refutes the
`Top` arm, and both remaining arms own `parent->rb_right`, so the second
conjunct reads it through the folded frame — as a view, with ownership
untouched. A cell only one possible arm owns is not published and the guard
stays undecided, which refuses the loop. The verified example is
`mdtests/rb_ascent_parent_link_guard.md`.

The descending walk that pushes those frames is `tree_leftmost` in
`examples/modeled-binary-tree`, verified with `decreases t;` on the focused
subtree; [larger examples](larger-examples.md#a-modeled-loop-end-to-end) walks
through the whole proof, and the same shape on the unchanged Linux `rb_first`
is `mdtests/rb_first_last.md`.

Unlike the numeric components, the structural descent is not a member of the
back-edge invariant bundle. The back edge decides it directly and names the
binder when it does not descend, as in
`mdtests/loop_decreases_rejects_same_instance.md`. Unfolding a layer and
refolding the same model under a fresh instance name is also insufficient:
progress is strict descent in the finite model, not a change of resource
identity. `mdtests/loop_decreases_rejects_rebuilt_layer.md` reaches this refusal
after successfully rebuilding the layer.

### Measures over a binder's model

Some loops re-fold their resource at every step instead of walking into a
child. The new instance is not contained in the old one, so no structural
descent exists, yet a number computed from the model still drops. Such a loop
ranks by a function of the model:

<!-- verified-example: mdtests/loop_measure_reads_a_model_function.md -->
```click
loop {
    owns c: chain(n);
    decreases chain_len(c.model);
    invariant n >= 0;
}
```

The component is an ordinary `Integer` ranking expression. It is
built from the loop binders' models and fields, constants, and pure Click
functions of them. Here `chain_len` is a recursive function with its own
`decreases`. Its two members join the back-edge invariant bundle like any
numeric component's: the value at the next head is at least zero, and it is
strictly less than the value at this head. Both are ordinary goals. The kernel
does not unfold the function or search for a proof. The usual route is to match
on the model so that its parts have names. State each side with `have`, by
`unfold` and `rewrite`. Apply a lemma for nonnegativity, typically one proved
once by structural `induct`. Then let `close()` close the comparison before
the back edge.

A `Nat`-valued function of the model ranks by its Integer image `to_integer`,
whose nonnegativity is the checked law `nat::to_integer_nonnegative`. Such a
measure owes only the decrease
(`mdtests/loop_measure_reads_a_nat_model_function.md`).

A model measure reads only models. One that also names a C local is refused
where it is declared, naming the local
(`mdtests/loop_decreases_model_function_rejects_a_c_local.md`), because the
local moves independently of the binders it would be ranked with. A model value
itself, such as `decreases c.model;` for a spec enum, has no order and is
refused with a pointer to the two forms that do rank by structure
(`mdtests/loop_decreases_rejects_an_unordered_model.md`). A back edge that
leaves the measure unchanged, or one that can drive an `Integer` measure below
zero, leaves its member open
(`mdtests/loop_decreases_model_function_must_decrease.md` and
`mdtests/loop_decreases_model_function_must_stay_nonnegative.md`).

### Opening a binder's model inside the body

Arm selection publishes the selected arm's cells, but `unfold(c)` needs the
constructor itself, and at an arbitrary loop head the binder's model is a
fresh symbolic value. A proof `match` on that model inside `maintain` supplies
it:

<!-- verified-example: mdtests/loop_body_proof_match_concise_proof.md -->
```click
maintain by {
    match c.model {
        Maybe::None => { contradiction(c.model == Maybe::None); },
        Maybe::Some(value) => {
            have Maybe::Some(value) == old(c.model) by {
                close() using { c.model == Maybe::Some(value); c.model == old(c.model); };
            }
            unfold(c);
            step();
            let c = fold(cell(node), { model: Maybe::Some(value) });
        },
    }
}
```

The live arm first states `Maybe::Some(value) == old(c.model)`: the refolded
model is the arm's binding, and the invariant `c.model == old(c.model)` needs
that binding related to the entry model at the back edge.

With nothing written after it, the arms of such a `match` do not rejoin.
Each arm executes one complete iteration, restores
the loop binder, closes the invariants, and satisfies the structural descent
on its own path, with the resource state that arm produced. An arm that
unfolds the binder and never folds it again fails at the back edge by name
even when its sibling succeeds
(`mdtests/loop_body_proof_match_arm_drops_binder.md`). An arm the invariants
exclude closes by `contradiction`; every remaining arm runs, and a `match`
that omits a constructor is refused exactly as at function entry
(`mdtests/loop_body_proof_match_missing_arm.md`).

`contradiction` does not have to be an arm's only tactic. It refutes the path
it stands on wherever on that path it stands, so an arm may first bridge the
refuting fact into its own terms — a `have`
(`mdtests/function_match_arm_closes_by_contradiction_after_a_have.md`, in a
`match` at the function's own level), or the `unfold` that exposes the fact at
all (`mdtests/do_while_returns_rebound_resources.md`, whose loop body's `Empty`
arm unfolds the binder first) — and close afterwards. A refuted path owes no
invariant and no measure, contributes
neither a back edge nor a loop exit, and nothing written after the
`contradiction` on it is executed or proved. The refutation is still decided
from the facts standing there: naming a proposition the path does not deny
leaves the arm open and is refused by the proposition as written
(`mdtests/preserve_arm_contradiction_needs_a_refuted_fact.md`).

`mdtests/loop_body_proof_match_two_live_arms.md` is the shape where both
constructors survive: the region splits, each arm certifies its own path, and
the preservation certificate is reassembled as the `match` that produced them.

A C `branch` inside a match arm rejoins its own C paths while retaining the
surrounding constructor case. Whole-claim expansion therefore keeps that
match around the arm's resource operations, including when the C branch
itself has no `ensuring` interface
(`mdtests/loop_preserve_branch_tactic.md`, `chain_countdown`).

What follows a split is checked once. Tactics written after a `match` or a
proof `if` in the body are never run once per arm, because every further
split would double that again. So when two arms are both still live at the
same point, they have to become one path before those tactics run:

- Arms that only reason, or that run the same statements and end holding the
  same resources, rejoin on their own, as they do in a function body
  (`mdtests/loop_preservation_case_after_step.md`).
- Arms that end holding different things rejoin through an interface:
  `match value ensuring { owns c: cell(node); } { ... }` names what the one
  path that leaves the `match` holds
  (`mdtests/loop_body_proof_match_ensuring_rejoins.md`).
- Arms that do neither are refused, by the tactic they would both reach
  (`mdtests/loop_body_proof_match_shared_continuation.md`). Give the `match`
  an interface, or write the rest of the iteration inside each arm.

Arms that reach those tactics at different points are different paths
of the C, one having stepped to a `break` and another to the body's end, say.
Each is finished its own way and nothing is repeated. An arm closed by
`contradiction` reaches nothing.

The invariants and the loop condition are the head's premises, so they also
refute arms. A premise that contradicts an arm's own binding-free fact says
the binder's model is not that constructor, and the body gets that as an
ordinary premise: the guard `n > 0` against a chain resource's `Nil` arm
`fact k == 0` publishes `c.model != Chain::Nil`, which is what lets the
`Nil` arm close by `contradiction` on the model instead of unfolding the
instance (`mdtests/loop_decreases_strict_descendant.md`).
The back edge publishes the same way, so a descent that unfolds a child under
a guard hands the next iteration the model fact that guard established. The
rule itself is in [resources](resources.md).

Refutation also runs where the body stands, not only at the head. A child the
body unfolded is often decided by a fact the body establishes afterwards — the
C local the next statement reads — so the case split a proof `match` issues,
and the `unfold` that opens a matched instance, both read the premises at that
frontier. A body that decrements and then asks whether it may step down again
closes the child's dead arm by `contradiction` on the child's model, and the
arm the `unfold` opened is published so the structural measure can still see
that the binder holds the child this path descended into
(`mdtests/loop_body_refutes_an_unfolded_child.md`).

A whole loop may also sit inside one proof `match` arm, which is how a fixup
that decides its cursor's constructor once at entry is written. The arm's
constructor equation is a premise of the path, not a different entry state:
the loop's entry projection, the checked body, and contract certification all
see the contract's own entry: `spin` in
`mdtests/loop_clause_reads_arm_bindings.md` runs its ranked loop inside the
`Node` arm and still certifies `ensures t.model == old(t.model)`.
The arm's bindings are in scope in the loop's clauses, as they are in any
term the arm writes: an invariant, a declared resource's arguments, and a
`decreases` measure may name the arm's pointer, integer, and model bindings,
and the clause is read with them resolved exactly as a `have` goal at the
loop's frontier is. The clause keeps its source text, which is what
expansion prints (`mdtests/loop_clause_reads_arm_bindings.md`). The same scope
reaches the loop's `initialize` and `maintain` bodies, at any nesting depth: a
`have` goal, a theorem argument, or an `unfold` target written in a phase body
may name the arm's bindings exactly as one written beside the `loop` may
(`mdtests/loop_phase_body_reads_arm_bindings.md`). Each phase is checked as its
own sub-proof, so this is the scope being attached to that sub-proof's root
rather than anything the phase body itself declares.

An invariant that fixes a pure function's value at the binder's model, such as
`invariant ctx_node_is(c.model, parent) == 1`, refutes no arm by itself. Only
an arm's own binding-free facts are compared with the premises. Finding which
predicate fact contradicts an arm would be a search, and the frontiers that
publish arms are checking steps. A proof that needs the exclusion states it,
`have c.model != Context::Top by ...`, or matches the model, and the frontier
then reads that exact fact (`mdtests/loop_head_predicate_does_not_decide_an_arm.md`).

### Ascending walks

A descending walk pushes context frames; an ascending one pops them. The loop
holds the same pair a Linux rbtree fixup loop holds — the focused subtree and
the frames above it — and each iteration consumes one frame:

<!-- verified-example: mdtests/loop_ascending_walk_to_root.md -->
```click
loop {
    owns c: pctx_at(node, parent);
    owns t: ptree_at(node, parent);
    decreases c;
    invariant t.model != HeapTree::Empty;
    invariant plug(c.model, t.model) == plug(old(c.model), old(t.model));
}
```

The body unfolds the frame, takes the C steps that move the cursor up, and
folds the node the frame owned into a larger focused subtree built from the
old focus and the frame's sibling. The measure is the context, because the
focused subtree grows while the context strictly loses a frame.

Both ends of such a walk come from arm refutation. At the head the guard
`parent != 0` refutes the `Top` frame's `fact parent == 0`, so the body's
proof `match` closes `Top` by contradiction. At the exit the same rule runs
with the failed guard: `parent == 0` refutes the `Left` and `Right` arms'
`fact parent != 0`, so the proof after the loop has `c.model == Context::Top`
and can `unfold` the frame without a `match` of its own. A loop exit publishes
refuted arms exactly as the head and the back edge do.

The walk then hands its final instances to the contract's produced binders by
refolding them under those names, at the arguments the exit reached. Those
arguments are the caller's view: `result` is the returned pointer, and the
root's parent is the null pointer constant rather than the parameter the body
reassigned.

A `void` walk has no `result`, and a parameter it reassigned still means the
value the caller passed, so neither names where such a walk ended. A cell the
contract owns does: a produced clause's cell reads are taken in the exit state,
so a fixup that owns `root->rb_node` produces `rb_at(root->rb_node)` and hands
the whole tree back at the position it linked, which is the same cell the
caller reads after the call
(`mdtests/rb_produces_through_the_root_cell.md`). The contract side of that
boundary is in [the language reference](../reference/language/index.md).

`old(name.field)` in an invariant is the function-entry instance of the
function-level binder of that name, whatever the body did to that instance
before the loop. A proof that unfolds and refolds the binder before the loop
does not change what `old(...)` means, even when it opens it before the
proof's first `step()`, where the C execution starts from a state that does
not hold the instance at all
(`mdtests/loop_invariant_old_model_when_the_unfold_precedes_execution.md`); an explicit `at(...)`
still names a point, and an instance the path did not hold there is an error.

Loop frames do not erase semantic lifetime state. A body that frees or
allocates heap storage, or calls a function whose contract consumes or
produces a resource, must leave the heap lifetime and resource context
unchanged on a continuing loop path. Click checks this in the kernel alongside
the ordinary invariant and frame obligations; a state change is rejected
rather than silently restored from the loop head. This prevents a later
iteration from using a block or ownership permission that a previous
iteration removed. When the post-body condition is provably false, the checked
post-body state is retained as a separate final exit instead. Thus a loop may
release heap storage on its last iteration without making that release appear
at an earlier loop head.

## Loop proof tactics

An explicit preservation proof starts at the loop head of an arbitrary iteration and must
traverse exactly one complete iteration. Straight-line bodies use one `step()`
per statement. In a proof-level `if`, `step()` enters a C branch from an exact
condition fact. Initialization
is non-executing because its point is already the first loop entry.

### What a `maintain` script accepts

A preservation script is the ordinary execution grammar: `step()` and the
other linear execution tactics, `have`, the resource operations, a proof-level
`if`, a proof `match` on a model, a `with` scope, and `branch` on the C `if`
at the frontier. The two conditional forms differ in where their arms go. A
proof `if` and a proof `match` never join: each arm runs its own complete
iteration to the loop rule, so each closes the invariants and satisfies the
measure on its own. `branch` joins its arms at the statement after the C `if`,
which is the cheaper form when they do rejoin — a body whose `if` only
chooses which link to write — and refuses when they cannot, because an arm
`break`s or `continue`s out of the join.

<!-- verified-example: mdtests/loop_preserve_branch_tactic.md -->
```click
maintain by {
    branch ensuring {
        fact t >= 0;
        fact t <= 100;
    } {
        true => { step(); }
        false => { step(); }
    }
    step();
}
```

A `branch` whose guard the path has already decided — the arm of a proof
`match` the body is in settles it — takes its one feasible arm and certifies
as that single path. It is the C `if` consumed on this path, not a case the
preservation leaf split at, so it charges the leaf's path no case
(`mdtests/loop_preserve_branch_tactic.md` has both shapes; the same C written
with bare `step()`s instead is
`mdtests/loop_decreases_strict_descendant.md`).

A tactic outside that grammar is refused by name rather than interpreted, and
so is a path that stops anywhere but the body's end, a `continue`, a `break`,
or a function `return`.

A body path that reaches `return` closes the function contract in that
`maintain` arm. Tactics written after the returning step, such as
`have result == 7 by close();`, apply only to that returned outcome.
The tactics after `loop` apply only to the continuing exit. A returning arm
is finished by the implicit closer, owned by `loop`, including when
preservation is automatically generated. Every returned outcome still
owes the function's postcondition and resource obligations. Expansion writes
its checked closing steps into the returning `maintain` arm, including for
natural cycles and nested loops.

A `maintain` script works like a function proof: when it ends, the loop's
back edge owes the whole invariant bundle, and each member is closed by
`close()`, as a function's exit closes each `ensures`. There is no tactic to
write for it; the retired `close_invariants` is rejected by the parser
(`mdtests/close_invariants_is_retired.md`).

<!-- verified-example: mdtests/c_decreases_count_up.md -->
```click
maintain by {
    step();
}
```

`click expand` prints the closure as one `have <member> by { ... }` per
member at the end of the `maintain` script, omitting members already
available as facts.

Stepping to the back edge is optional too. A path whose tactics run out
inside the body runs the rest of it as an omitted `maintain` runs a whole
body: straight-line statements are stepped, and a C `if` the path does not
decide splits into separate paths, as the implicit tail splits it. A statement whose successors are path cases,
such as a comparison stored in a local, splits on their condition as
the implicit tail does
(`mdtests/an_omitted_preserve_splits_a_comparison_assigned_to_a_local.md`).
Each path that reaches the body's end, a
`continue` or a `break` closes as a written one does, so a script holds only
the steps that need proof work and ends where that work ends
(`mdtests/preserve_runs_the_rest_of_the_body.md`). Expansion writes the steps
that ran.

The back edge closes every member with `close()` alone, which reads the facts
in scope like any other `close()`; each member is guarded by the invariants
declared before it. Each member
is raised as its clause writes it, as a function's exit closes each `ensures`
as written: an invariant over the back-edge locals, and the descent member of
`decreases m` as `m < at(<iteration entry>, m)`, a tuple's as the
disjunction over pivots with the earlier components tied. That closes an
unsigned or 64-bit bound such as `i <= n` after `i += 1` from the guard
`i < n`, and the descent of `n - i`
(`mdtests/back_edge_closes_an_unsigned_bound_from_the_guard.md`,
`mdtests/a_64_bit_countdown_closes_its_back_edge.md`). A member `close()`
misses is named in the refusal; prove it, or a fact it needs, with
`have <invariant> by { ... }` before the back edge, as for an `ensures`.

The bundle is a conjunction with one member per declared clause, in
declaration order. A clause that reads memory is preceded by members for what
its reads owe: the viewability of each cell it reads at the back edge, and at
function entry for a read under `old`. A member is guarded by everything
before it that it may rely on: the path facts of its lowering, the read
obligations raised so far, and each earlier clause as written. An earlier
clause is a guard in its bare form rather than as the whole earlier member,
so the bundle gains one guard per earlier declaration instead of doubling
with each one (`mdtests/loop_frame_keeps_two_header_cells_of_a_field_map.md`).

When the whole bundle has no source form, for instance because one member is
at the loop entry beside members at the iteration entry, each member is
raised on its own at the one point it names, which is how the expanded
proof's `have` writes it, so `intro` names a member's quantified index as that
`have` does.

Successful initialization and preservation proofs certify and apply a
verified loop rule. The enclosing proof is already at the loop exit when the
`loop` tactic returns; there is no later step and no need to reconstruct a path
from function entry.

Explicit phase tactics keep their own source locations for profiling and
expansion. Omitted phase automation is attributed to the `loop` keyword.

Most simple proofs avoid these details. Larger proofs need them whenever
the loop summary is the central part of the proof.

### The frontier of an unfinished `maintain`

A long body is written a few tactics at a time. A path whose tactics stop
inside the body runs the rest of it implicitly, as above; when that rest
does not run, for instance because a statement ahead needs a fact the path
does not have, the script is unfinished rather than wrong. Answering that
with the bare one-iteration rule hides how far the body actually got, so an
unfinished script is refused with the frontier it reached instead, followed
by why the rest did not run:

- the statement the path stands before, and its statement index — leading block
  ends are stepped over, so this is the next statement the C would run;
- the tactic that left it there, by index and name. A proof `match` arm
  written with no tactics reaches the region's end at once, and is named as
  such ("after tactic 0 `match, inside an arm with no tactics`") rather than
  as if the `match` were the last thing that ran
  (`mdtests/preserve_empty_arm_reports_frontier.md`);
- the ends still ahead of it on *this* path: the body's end, and each `break`
  and `continue` the rest of the body still holds. Only this loop's own exits
  are counted, since a nested loop or `switch` owns the ones written inside it;
- what the script's other paths have already closed, counted by the end each
  reached.

```text
`walk.contract` stopped inside the loop body: the frontier is at statement 5,
`i = (i - 1)`, after tactic 1 `step`; still ahead on this path: the body's end.
Already complete: 1 at a `break`. Every path a `maintain` opens must end at the
body's end, a `continue`, or a `break`
```

`mdtests/loop_preserve_frontier_report.md` is that case, and
`mdtests/loop_preserve_frontier_report_multi_exit.md` is a body whose `break`
arm is closed while a `continue` and the body's end are still ahead.

The report is for a body that ran out of written tactics. A tactic that *fails*
stops the body where it stands and its own diagnostic is what the author sees
(`mdtests/loop_preserve_tactic_failure_reported.md`). The one-iteration rule is
still what refuses a body that is complete and wrong without reaching one of
those endings, because such a path did not stop inside the body at all.

An unfinished path does not stop the region's other paths. Each arm of a
proof `match` that does reach an ending still closes its invariants and its
measure, and a failure there is reported before the unfinished sibling's
frontier: a back-edge member a finished arm fails to close is named while the
next arm is still being written, rather than staying silent until every arm
is finished (`mdtests/preserve_finished_arm_checked_before_frontier.md`).
