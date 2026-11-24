# A branch split inside an inlined call is not answered with `outcomes`

`step()` executes the whole inlined `set(p, c)`, and its `if (c)` is
undecided, so the call has two successors. Both of them return. The refusal
names the condition and the proof `if` that splits on it.

It used to add a second suggestion after that one,

```text
`step()` cannot choose between the two successors of this call. Use `outcomes` at this point:
outcomes {
    returned => { }
    threw => { }
}
```

which is the split for a call that may throw: one returning edge and one
caught exceptional edge. Nothing here throws, so neither arm can be taken and
the advice sends the reader to a tactic that cannot apply. It is now offered
only when exactly one of the two successors is a `Throw`.

```c filename=step_branch_split_in_inline_call_does_not_offer_outcomes.c
static inline void set(int32 *p, int32 c) {
    if (c)
        *p = 1;
    else
        *p = 2;
}

void choose(int32 *p, int32 c) {
    set(p, c);
}
```

```click
verifying "step_branch_split_in_inline_call_does_not_offer_outcomes.c";

void choose(int32* p, int32 c) {
    owns p[0..1];
    ensures p[0] == 1 or p[0] == 2;
} by {
    step();
    close();
}
```

```expect
fail: The implicit tail makes this split itself where the script ends.
proof context:
```
