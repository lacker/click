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

The rule is the function-level structural rule applied at the back edge: the
instance the binder ends holding must be a direct contained child, in the
exact resource definition, of the instance it held at the loop head, carrying
the submodel that child names. A model is a finite inductive term, so a
strictly smaller submodel at every back edge is well-founded. No counter, size
function, or automatic unfolding takes part, and a descending loop decreases
its subtree binder while an ascending one decreases its context binder,
because a rotation may grow the focused subtree while the context strictly
loses a frame.

Which arm names the children is decided by the loop's invariants, playing the
part of a contract's requirements. That is the same arm selection contract
lowering performs, so the measure needs a `match model` resource whose
constructor the invariants pin down; a binder whose constructor they leave
open is refused by name rather than guessed. The invariants also publish the
selected arm's cells as read authority at the loop head, which is what lets a
guard such as `root->left != 0` read through the focused subtree the binder
holds.

Unlike the numeric components, the structural descent is not a member of the
back-edge invariant bundle. The back edge decides it directly and names the
binder when it does not descend, as in
`mdtests/loop_decreases_rejects_same_instance.md`.

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

`mdtests/loop_body_proof_match_two_live_arms.md` is the shape where both
constructors survive: the region splits, each arm certifies its own path, and
the preservation certificate is reassembled as the `match` that produced them.

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
