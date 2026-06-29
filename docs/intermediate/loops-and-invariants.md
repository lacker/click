# Loops And Invariants

Loops require summaries. Click cannot prove a symbolic loop by unrolling it
forever.

A loop invariant is a fact that must hold:

- before the first iteration,
- at the start of every iteration,
- and after one iteration preserves it.

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
loop 0 {
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
loop 0 {
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
    loop_vc(loop 0);
    close();
}
```

`loop_vc(loop N)` checks the generated verification conditions for loop `N`.

`frame(loop N)` proves a loop effect summary and exposes it for later proof
steps.

Most beginner code avoids these details. Intermediate Click needs them whenever
the loop summary is the central part of the proof.
