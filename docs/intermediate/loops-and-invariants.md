# Loops And Invariants

Loops require summaries. Click cannot prove a symbolic loop by unrolling it
forever.

A loop invariant is a fact that must hold:

- before the first iteration,
- at the start of every iteration,
- and after one iteration preserves it.

In Click terms, `loop(N)` names a loop code region. The invariant is checked at
program points associated with that region. Since a loop head can be reached
more than once, those program points can have many runtime visits.

A labeled loop can also expose its entry visit to the invariant:

```click
for loop(0) as drain {
    invariant at(drain.entry, n) >= 0;
}
```

This means the value of `n` at the visit just before the loop region starts.

For a simple counter loop:

```c
int32 count_to(int32 n) {
    int32 i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

the proof needs bounds on `i`:

```click
for loop(0) {
    invariant i >= 0;
    invariant i <= n;
}
```

The full induction syntax names its two obligations explicitly:

```click
for loop(0) {
    invariant i >= 0;
    invariant i <= n;

    initialize by auto;
    preserve by {
        execute_step();
        simp();
    }
}
```

`initialize` is a pure proof of all invariants at the actual loop entry. It can
use `apply`, nested `have`, proof-level `if`, `unfold`, and `simp`, but cannot
execute C or transform resources. `preserve` assumes all invariants and the loop
condition, executes one complete body iteration, and proves all invariants
again. Either proof may be omitted; an omitted phase uses `auto`.

## What Invariants Do

An invariant is the bridge from the loop body to the postcondition. If the
postcondition needs `i == n` after the loop, Click must know enough at loop exit
to combine:

- the invariant facts,
- the failed loop condition,
- and the function requirements.

## Memory Loops

Pointer-writing loops often need both arithmetic invariants and memory facts:

```click
for loop(0) {
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

## Loop Proof Steps

An explicit preservation proof starts at an arbitrary loop-head visit and must
traverse exactly one complete iteration. Straight-line bodies use one `step()`
or `execute_step()` per statement. In a proof-level `if`, `step()` enters a C
branch from an exact condition fact; `execute_step()`, `execute_then_step()`,
and `execute_else_step()` provide contextual branch reasoning. Initialization
is non-executing because its execution point is already the first loop entry.

Successful initialization, preservation, and effect proofs certify a verified
loop rule. Execution applies that rule directly; there is no separate proof step
for rechecking the loop's verification conditions.

`frame(loop(N))` checks a loop's certified write summary against its declared
effect using exact available bounds, then exposes the summary for later proof
steps. Labeled code regions can be used in the same positions. A loop effect
clause may use contextual `by frame` when those bounds should be derived
automatically.

Most beginner code avoids these details. Intermediate Click needs them whenever
the loop summary is the central part of the proof.
