# A loop invariant may only read the binders the loop declares

The loop declares `owns a: tag(0);`, so `b` stays with the enclosing frame for
the whole loop and the body cannot see it. An invariant that reads `b.mark`
is refused rather than silently read from the entry state.

```c filename=loop_invariant_rejects_undeclared_binder.c
int32 spin(int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "loop_invariant_rejects_undeclared_binder.c";

resource tag(k: int32) {
    field mark: int32;
}

int32 spin(int32 n) {
    requires n >= 0;
    owns a: tag(0);
    owns b: tag(1);
    ensures b.mark == old(b.mark);
} by {
    step();
    step();
    loop {
        owns a: tag(0);
        invariant i >= 0;
        invariant i <= n;
        invariant b.mark == old(b.mark);

        initialize by simp;
        preserve by {
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
fail: loop 0 invariant 2 preservation: could not be read at the loop head
```
