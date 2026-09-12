# A loop binder must name exactly one instance

The function holds two `tag(0)` instances. The loop declares a binder at the
same arguments, so nothing says which of the two it takes, and the loop head
refuses it instead of choosing.

```c filename=loop_binder_rejects_ambiguous_instance.c
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
verifying "loop_binder_rejects_ambiguous_instance.c";

resource tag(k: int32) {
    field mark: int32;
}

int32 spin(int32 n) {
    requires n >= 0;
    owns a: tag(0);
    owns b: tag(0);
    ensures a.mark == old(a.mark);
} by {
    step();
    step();
    loop {
        owns t: tag(0);
        invariant i >= 0;
        invariant i <= n;

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
fail: loop binder `t` matches 2 owned `tag` instances at its arguments
```
