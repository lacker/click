# The one-successor refusal names the guard, not the whole loop node

Both conjuncts are readable here, so the guard really does produce two loop
exits and the `loop` tactic refuses: it certifies one successor. The refusal
has to say which statement it is on in the spelling the C uses. Printing the
`While` node itself would attach the body, every lowered invariant and effect
check, and every resource spec to the message, which is an internal-state dump
rather than a diagnostic.

```c filename=loop_successor_refusal_names_the_guard.c
int32 uprec_owned(int32 a, int32 *p) {
    while (a != 0 && p[0] != 0) {
        a = 0;
    }
    return a;
}
```

```click
verifying "loop_successor_refusal_names_the_guard.c";

int32 uprec_owned(int32 a, int32* p) {
    requires a >= 0;
    requires a <= 10;
    views p[0..1];
    ensures result == 0;
} by {
    loop {
        views p[0..1];
        invariant a >= 0;
        invariant a <= 10;
    }
    step();
    simp();
}
```

```expect
fail: requires exactly one statement successor for `while ((a != 0) && (p[0] != 0))`, got 2
```
