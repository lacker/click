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
nonempty int32 ranking expression or lexicographic tuple:

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
treated as a terminating phase when checking its enclosing loop; aliases for
outer ranking variables written by that phase are forgotten, and the outer
invariants must establish the resulting ranking components are nonnegative.
When a loop contains a numeric recursive call, the loop and the recursive edge
need separate evidence: the loop must have its own ranking, and the
function-level `decreases` measure must strictly decrease at every recursive
edge. The loop guard is used when proving the recursive argument is
nonnegative. The numeric function-level measure must remain unchanged by the
loop body; calls whose descent depends on a changing lexicographic caller
measure remain unsupported. A read-only structural-resource call inside a
ranked loop is supported when the parent resource is observed before the loop
and the loop effect is declared `immutable by frame`; the call must still
receive a direct contained child. Pointer-valued branch guards are not scalar
ranking facts, so the ranking checker checks the scalar measure on every path
without importing those pointer comparisons. Resource-consuming or mutating
structural calls across a loop back edge remain tracked in
`issues/recursive-resources.md`.

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
    invariant i >= 0;
    invariant i <= n;
    mutable p[0..n] by frame;

    step {
        mutable p[i..i + 1] by frame;
    }
}
```

The arithmetic invariants prove access bounds. The frame clauses summarize what
memory the loop may write.

Loop frames do not erase semantic lifetime state. A body that frees or
allocates heap storage, or calls a function whose contract consumes or
produces a resource, must leave the heap lifetime and resource context
unchanged on a continuing loop path. Click checks this in the kernel alongside
the ordinary invariant and effect obligations; a state change is rejected
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

Successful initialization, preservation, and effect proofs certify and apply a
verified loop rule. The enclosing proof is already at the loop exit when the
`loop` tactic returns; there is no later `summarize(loop(N))` step and no need
to reconstruct a path from function entry.

A loop effect clause may use contextual `by frame` when its exact bounds should
be derived automatically. Explicit phase and effect tactics keep their own
source locations for profiling and expansion. Omitted phase and effect
automation is attributed to the `loop` keyword.

Most simple proofs avoid these details. Larger proofs need them whenever
the loop summary is the central part of the proof.
