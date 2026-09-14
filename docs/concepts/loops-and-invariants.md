# Loops and invariants

Loops require summaries. Click cannot prove a symbolic loop by unrolling it
forever.

A loop invariant is a fact that must hold:

- before the first iteration,
- at the start of every iteration,
- and after one iteration preserves it.

These checks establish partial correctness, not termination. They prove that
every finite iteration prefix is safe and that the invariant is available if
the loop exits. A constant-true service loop can therefore have a useful
invariant even though it has no exit state.

When termination itself matters, the loop tactic may additionally declare a
`decreases` clause. The clause is one expression, and what it names decides
which measure it is: a nonempty int32 ranking expression, a lexicographic
tuple of them, or one of the loop's own resource binders. The same uniform
rule applies to a C function's own `decreases`; there is no `decreases
resource` spelling anywhere.

<!-- verified-example: mdtests/count_to_n_loop_invariant.md -->
```click
loop {
    decreases remaining;
    invariant remaining >= 0;
}
```

<!-- verified-example: mdtests/c_decreases_lexicographic_loop.md -->
```click
loop {
    decreases (outer, inner);
    invariant outer >= 0;
    invariant inner >= 0;
}
```

The expression is checked at each continuing body path: the loop guard and
the available function preconditions and invariants must establish that every
component is nonnegative. A tuple decreases lexicographically: an earlier
component must remain equal and a later component must be strictly smaller at
some pivot. This supports count-up loops as well as countdowns, for example
`decreases limit - index;` when the body increments `index`. Each component is
checked as C int32 arithmetic, so its arithmetic must also be defined under
those assumptions. This produces separate termination evidence; it does not
change what an invariant or a postcondition means. Loops without `decreases`
remain valid partial-correctness proofs. A separately ranked nested loop is
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
loop body; calls whose descent depends on a changing lexicographic caller
measure remain unsupported. A read-only structural-resource call inside a
ranked loop is supported when the parent resource is observed before the loop;
the call must still receive a direct contained child. Pointer-valued branch guards are not scalar
ranking facts, so the ranking checker checks the scalar measure on every path
without importing those pointer comparisons. Resource-consuming or mutating
structural calls across a loop back edge remain tracked in the hard-bucket
`issues/recursion.md`.

Termination is also a claim about everything the loop body calls: every
reachable loop, recursive cycle, and callee needs a checked ranking proof. A
callee with a contract answers with a verified rule of its own. A
header-provided `static inline` helper has no contract boundary — its body
executes at the call site — so it is read as a node of the caller's own call
graph instead. A helper whose body is straight-line, with no loop, no
recursion, and no call to anything not itself terminating, terminates by
construction, so a ranked loop may call one:
`mdtests/c_decreases_loop_inline_helper.md`, and the rbtree ascent of
`mdtests/rb_ascending_walk_to_root.md`, which climbs through the unchanged
Linux `rb_parent` under `decreases c;`. A helper carrying a loop still needs
that loop ranked and certified, and a recursive helper is a cycle needing a
checked rule; both are refused otherwise
(`mdtests/c_decreases_rejects_inline_helper_loop.md` and
`mdtests/c_decreases_rejects_recursive_inline_helper.md`). A helper's own
ranked loop is planned under the translation-unit-qualified name its body
executes under rather than the ordinary spelling its sidecar contract uses,
which is what lets the plan reach the function the call site names
(`mdtests/inline_helper_ranked_loop.md`).

The [`perpetual-service`](https://github.com/lacker/click/tree/master/examples/perpetual-service) example
combines this partial-correctness boundary with an opaque verified call and a
composite resource transferred through every iteration.

An execution proof has a frontier: the boundary between C that has already
been checked and C that remains. `loop { ... }` handles the C loop exactly at
that frontier. It does not name a loop by source-order number and does not jump
forward to find one. If the frontier is not at a loop, the tactic fails.

The tactic checks initialization and one arbitrary iteration, constructs a
kernel-checked loop rule, applies that rule once, and advances the enclosing
frontier to the loop exit. Since a loop head can be reached more than once, the
preservation proof is about an arbitrary visit rather than one concrete
iteration.

A labeled loop can also expose its entry visit to the invariant:

<!-- verified-example: mdtests/count_to_n_loop_invariant.md -->
```click
loop as drain {
    invariant at(drain.entry, n) >= 0;
}
```

This means the value of `n` at the visit just before the loop region starts.

For a simple counter loop:

<!-- verified-example: mdtests/count_to_n_loop_invariant.md -->
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

<!-- verified-example: mdtests/count_to_n_loop_invariant.md -->
```click
by {
    step();
    step();
    loop {
        invariant i >= 0;
        invariant i <= n;
    }
    step();
}
```

The full induction syntax names its two obligations explicitly:

<!-- verified-example: mdtests/count_to_n_loop_invariant.md -->
```click
loop {
    invariant i >= 0;
    invariant i <= n;

    initialize by auto;
    preserve by {
        step();
        simp();
    }
}
```

`initialize` is a pure proof of all invariants at the actual loop entry. Its
script may use exactly `unfold(predicate)`, `apply(theorem(args))`, `have`,
`assumption()`, `normalize()`, `rewrite(...)`, `simp()`, and proof-level `if`;
anything else is rejected with `` `initialize` is a pure proof and cannot use
`<tactic>` ``. `preserve` assumes all invariants and the loop condition,
executes one complete body iteration, and proves all invariants again. Either
proof may be omitted; bounded automation owned by the `loop` keyword supplies
an omitted phase. Expanding that keyword writes all omitted phases explicitly.

## How an `initialize` script divides up

Each invariant gets its own entry goal, so an `initialize by { ... }` script is
read as three parts, in this order:

- a leading run of `unfold(predicate)` and `have` steps that name something
  other than an invariant. These are *helpers*: each is proved once, where it
  is written, and its fact is available to everything below it.
- one `have` per declared invariant, in declaration order, naming the
  invariant exactly as the `loop` head spells it. Such a `have` is that
  invariant's own proof, and no other invariant reads it.
- an optional trailing `assumption()` or `simp()`.

A script that does not name the invariants individually — `initialize by
simp;`, or a helper prefix followed by `simp()` — is one shared proof: every
invariant's entry goal is proved by the same remaining steps, with the helper
facts already available.

That division is what expansion prints. A smart tactic inside an invariant's
own `have` expands to the same `have` with a checked body, left where it was
written; a trailing `simp()` that stands for the rest of the phase expands to
one `have` per invariant, and the helpers above it are not copied into them. A
`simp()` written after the invariants are already named contributes nothing,
so expanding it removes it. `preserve by simp;` is the same whole-phase shape
one phase over, and expands to the planned preservation proof.

## What invariants do

An invariant is the bridge from the loop body to the postcondition. If the
postcondition needs `i == n` after the loop, Click must know enough at loop exit
to combine:

- the invariant facts,
- the failed loop condition,
- and the function requirements.

The failed condition describes an exit *if one occurs*. Invariant preservation
does not prove that such an iteration is eventually reached. Termination needs
a separate well-founded argument; ordinary C verification does not require
one.

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
    cases(a == 0 or p[0] == 0) {
        contradiction(a == 0);
    } {
        assumption();
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

### `break` and `continue` in the body

One certified iteration is a path that reaches the body's end, a `continue`, or
a `break`. A path that stops anywhere else has not been proved and the loop is
refused — but a body that merely is not written yet is refused with a *report*
of where it got to rather than with the bare rule; see
[the frontier of an unfinished `preserve`](#the-frontier-of-an-unfinished-preserve).

A `continue` is the back edge, reached early. Everything the body's end owes is
owed there: the loop's binders are bound again on the state the `continue`
reached, the invariants are closed there with `close_invariants()` written
after the `continue` is stepped, and a declared measure must have descended
there.

<!-- verified-example: mdtests/loop_body_continue_back_edge.md -->
```click
preserve by {
    step();
    step();
    close_invariants();
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
one arm leaves the loop, so it refuses and names the proof-level spelling
(`mdtests/loop_body_break_in_branch_arm_rejected.md`).

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
visit — the rule of [modeled instances in
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

A cell the exits wrote differently is a cell folded into one of the declared
binders, since the body owns nothing else, and a proof after the loop reads it
back through that binder's model. A loop that declares no binder has nothing to
read such a cell through, and the difference is refused naming the cell
(`mdtests/loop_break_exit_unowned_cell_rejected.md`).

What every exit states survives the join as an ordinary fact, so a claim that
does not distinguish the exits needs nothing special
(`mdtests/loop_break_exit_refold_join.md`). A claim that does distinguish them
is read off the exported disjunction with `cases`:

<!-- verified-example: mdtests/loop_break_exit_binder_model_join.md -->
```click
have c.color == Color::Red or c.color == Color::Black by {
    cases((flag == 0 and c.color == Color::Red and p->shade == 0) or (c.color == Color::Black and p->shade == 1)) {
        simp();
    } {
        simp();
    }
}
```

That is a `while (true)` whose two `break`s paint the node a different colour
and refold the binder before leaving: the model of `c` and the byte in
`p->shade` are both fresh in the successor, and the disjunction is what ties
them back to the two ways out. A local the exits disagree on works the same way
(`mdtests/loop_body_break_exit_joined_state.md`), and a claim only one exit
supports still fails
(`mdtests/loop_body_break_exit_joined_state_rejected.md`).

A guard-false exit stands at the loop head, where the locals the body writes
are fresh names of their own. Its own facts are therefore restated about the
successor's names before they are disjoined — valid because that exit's own
disjunct is the equation saying the two are the same value — so the disjunction
speaks in names a proof after the loop can spell. A `break` exit's facts about
the *head's* values are left as they are; they are true, but a proof after the
loop cannot name what they are about, so a `cases` over such a disjunction is
out of reach.

## Memory loops

Pointer-writing loops often need both arithmetic invariants and memory facts:

<!-- verified-example: mdtests/count_to_n_loop_invariant.md -->
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

The head is an arbitrary visit, so the model `c` carries there is arbitrary
too. Only the invariants say anything about it, and `old(c.count)` still means
the function-entry model of the function's own binder of that name. There is
no loop-entry snapshot of a model.

The body holds `c` and works with the ordinary proof operations. Here one
iteration opens the instance, writes the cell it owns, and folds it again with
the model that write produced:

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

<!-- verified-example: mdtests/loop_binder_counter_model.md -->
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
        owns c: counter(p);
        invariant i >= 0;
        invariant i <= n;
        invariant c.count == old(c.count) + i;

        initialize by simp;
        preserve by {
            unfold(c);
            step();
            step();
            let c = fold(counter(p), { count: old(c.count) + i });
            close_invariants();
        }
    }
    have i == n by simp;
    execute();
    simp();
}
```

The binder's arguments are read where they are used. The head builds the
binder's instance at the loop's own havocked values, so a cursor the body
reassigns is already the head's cursor, and `close_invariants()` reads the
clause again in the state the body reached. That is what lets a body hand a
child to the next iteration: after `root = root->left`, an
`owns sub: tree_at(root);` binder names the subtree at the new cursor by
proved argument equality.

`close_invariants()` selects the instance the same way the head did, with the
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
over the constructors the path spelled out, not a search for one, and a back
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

### Opening a binder's model inside the body

Arm selection publishes the selected arm's cells, but `unfold(c)` needs the
constructor itself, and at an arbitrary loop head the binder's model is a
fresh symbolic value. A proof `match` on that model inside `preserve` supplies
it:

<!-- verified-example: mdtests/loop_body_proof_match.md -->
```click
preserve by {
    match c.model {
        Maybe::None => { contradiction(c.model == Maybe::None); },
        Maybe::Some(value) => {
            unfold(c);
            step();
            let c = fold(cell(node), { model: Maybe::Some(value) });
            close_invariants();
        },
    }
}
```

The arms of such a `match` do not rejoin. A preservation path never joins
across the back edge, so each arm executes one complete iteration, restores
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
refuting fact into its own spelling — a `have`
(`mdtests/preserve_arm_contradiction_after_a_have.md`), or the `unfold` that
exposes the fact at all
(`mdtests/preserve_arm_contradiction_after_an_unfold.md`) — and close
afterwards. A refuted path owes no invariant and no measure, contributes
neither a back edge nor a loop exit, and nothing written after the
`contradiction` on it is executed or proved. The refutation is still decided
from the facts standing there: naming a proposition the path does not deny
leaves the arm open and is refused by the proposition as written
(`mdtests/preserve_arm_contradiction_needs_a_refuted_fact.md`).

`mdtests/loop_body_proof_match_two_live_arms.md` is the shape where both
constructors survive: the region splits, each arm certifies its own path, and
the preservation certificate is reassembled as the `match` that produced them.

The invariants and the loop condition are the head's premises, so they also
refute arms. A premise that contradicts an arm's own binding-free fact says
the binder's model is not that constructor, and the body gets that as an
ordinary premise: `invariant node != 0` against a list resource's `Nil` arm
`fact p == 0` publishes `l.model != CellList::Nil`, which is what lets the
`Nil` arm close by `contradiction` on the model instead of unfolding a cell
the arm does not own (`mdtests/loop_head_refuted_arm_closes_the_match.md`).
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
see the contract's own entry (`mdtests/rb_ascending_walk_in_entry_match.md`).
The arm's bindings are in scope in the loop's clauses, as they are in any
term the arm writes: an invariant, a declared resource's arguments, and a
`decreases` measure may name the arm's pointer, integer, and model bindings,
and the clause is read with them resolved exactly as a `have` goal at the
loop's frontier is. The clause keeps its written spelling, which is what
expansion prints (`mdtests/loop_clause_reads_arm_bindings.md`). The same scope
reaches the loop's `initialize` and `preserve` bodies, at any nesting depth: a
`have` goal, a theorem argument, or an `unfold` target written in a phase body
may name the arm's bindings exactly as one written beside the `loop` may
(`mdtests/loop_phase_body_reads_arm_bindings.md`). Each phase is checked as its
own sub-proof, so this is the scope being attached to that sub-proof's root
rather than anything the phase body itself declares.

An invariant that fixes a pure function's value at the binder's model refutes
arms too, and it is the invariant a model keyed by its own payload needs: the
arms speak about their bindings, while the guard speaks about a C local, and
the predicate is what relates the two. `invariant list_head_is(l.model, node)
== 1` with `invariant node != 0` refutes the `Nil` arm, because the declared
body at `CellList::Nil` is `if node == 0 { 1 } else { 0 }` and this path
decides it to be `0`
(`mdtests/loop_head_predicate_refutes_an_arm.md`). The same invariant read at
the exit refutes the arms *with* bindings, using the arm's own facts about
them, and when one field-free arm is left the exit learns what the model is
(`mdtests/contract_predicate_refutes_a_framed_arm.md`). A predicate that is
the same at both constructors decides nothing and the arm stays live
(`mdtests/loop_head_predicate_does_not_decide_an_arm.md`).

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
does not change what `old(...)` means
(`mdtests/loop_invariant_old_model_after_refold.md`), and neither does opening
it before the proof's first `step()`, where the C execution starts from a state
that does not hold the instance at all
(`mdtests/loop_invariant_old_model_when_the_unfold_precedes_execution.md`,
`mdtests/loop_invariant_old_field_after_a_refold.md`); an explicit `at(...)`
snapshot still names a state, and an instance it does not hold is an error
there.

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

An explicit preservation proof starts at an arbitrary loop-head visit and must
traverse exactly one complete iteration. Straight-line bodies use one `step()`
or `step()` per statement. In a proof-level `if`, `step()` enters a C
branch from an exact condition fact; `step()`, `step()`,
and `step()` provide contextual branch reasoning. Initialization
is non-executing because its program point is already the first loop entry.

### What a `preserve` script accepts

A preservation script is the ordinary execution grammar: `step()` and the
other linear execution tactics, `have`, the resource operations, a proof-level
`if`, a proof `match` on a model, an `open` scope, and `branch` on the C `if`
at the frontier. The two conditional forms differ in where their arms go. A
proof `if` and a proof `match` never join: each arm runs its own complete
iteration to the loop rule, so each closes the invariants and satisfies the
measure on its own. `branch` joins its arms at the statement after the C `if`,
which is the cheaper spelling when they do rejoin — a body whose `if` only
chooses which link to write — and refuses when they cannot, because an arm
`break`s or `continue`s out of the join.

<!-- verified-example: mdtests/loop_preserve_branch_tactic.md -->
```click
preserve by {
    branch {
        ensuring {
            fact t >= 0;
            fact t <= 100;
        }
        then { step(); }
        else { step(); }
    }
    step();
    close_invariants();
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
so is a path that stops anywhere but the body's end, a `continue`, or a
`break`.

A `preserve` script ends by discharging the whole invariant bundle at the loop's
back edge. `close_invariants()` is the surface tactic for that step. It is
accepted only inside `preserve by { ... }` — elsewhere it fails with
`` `close_invariants` is only available in a loop-region proof `` — and at most
once on a path.

<!-- verified-example: mdtests/count_to_n_loop_invariant.md -->
```click
preserve by {
    step();
    close_invariants();
}
```

Writing it is optional. If a `preserve` script does not close the bundle,
Click appends the closer implicitly after the last written tactic. The
expanded proof contains an explicit `close_invariants` leaf either way, so it
always appears in an expanded proof.

Successful initialization and preservation proofs certify and apply a
verified loop rule. The enclosing proof is already at the loop exit when the
`loop` tactic returns; there is no later `summarize(loop(N))` step and no need
to reconstruct a path from function entry.

Explicit phase tactics keep their own source locations for profiling and
expansion. Omitted phase automation is attributed to the `loop` keyword.

Most simple proofs avoid these details. Larger proofs need them whenever
the loop summary is the central part of the proof.

### The frontier of an unfinished `preserve`

A long body is written a few tactics at a time, and until its last path reaches
one of the body's ends the script is unfinished rather than wrong. Answering
that with the bare one-iteration rule hides how far the body actually got, so
an unfinished script is refused with the frontier it reached instead:

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
Already complete: 1 at a `break`. Every path a `preserve` opens must end at the
body's end, a `continue`, or a `break`
```

`mdtests/loop_preserve_frontier_report.md` is that case, and
`mdtests/loop_preserve_frontier_report_multi_exit.md` is a body whose `break`
arm is closed while a `continue` and the body's end are still ahead.

The report is for a body that ran out of written tactics. A tactic that *fails*
stops the body where it stands and its own diagnostic is what the author sees
(`mdtests/loop_preserve_tactic_failure_reported.md`). The one-iteration rule is
still what refuses a body that is complete and wrong — one that leaves the loop
through a `return`, for instance — because such a path did not stop inside the
body at all.
