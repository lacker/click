# An unestablished loop invariant fails at its entry obligation

The loop invariant `i >= 1` does not hold at entry, where `i` is zero. The
entry obligation is emitted rather than discharged inside lowering, so the
initialization proof fails at that obligation and the diagnostic names it.

```c filename=loop_entry_invariant_not_established.c
int32 loop_entry_invariant_not_established(int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "loop_entry_invariant_not_established.c";

int32 loop_entry_invariant_not_established(int32 n) {
    requires n >= 0;
    ensures result >= 0;
} by {
    step();
    step();
    loop {
        invariant i >= 1;
        initialize by simp;
        preserve by simp;
    }
    step();
    simp();
}
```

```expect
fail: loop 0 invariant 0 entry
```
