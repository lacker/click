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
    invariant at(drain.entry, n) >= 0 by auto;
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
    invariant i >= 0 by auto;
    invariant i <= n by auto;
}
```

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
    invariant i >= 0 by auto;
    invariant i <= n by auto;
    mutable p[0..n] by frame;

    step {
        mutable p[i..i + 1] by frame;
    }
}
```

The arithmetic invariants prove access bounds. The frame clauses summarize what
memory the loop may write.

## Loop Proof Steps

Some loop proofs call loop-specific steps:

```click
by {
    loop_vc(loop(0));
    close();
}
```

`loop_vc(loop(N))` checks the generated verification conditions for loop code
region `N`.

`frame(loop(N))` proves a loop effect summary and exposes it for later proof
steps. Labeled code regions can be used in the same positions.

Most beginner code avoids these details. Intermediate Click needs them whenever
the loop summary is the central part of the proof.
