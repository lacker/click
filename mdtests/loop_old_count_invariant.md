# loop invariant lowers old-state stdlib count

This checks that `old(...)` in a loop invariant re-elaborates its body in the
entry-state spec context. In particular, `old(count(...))` reaches the stdlib
`count` function and keeps its `.fold` as pure spec/core over entry memory.

```c filename=loop_old_count_invariant.c
int32 loop_old_count_invariant(int32 p[3]) {
    int32 i;
    i = 0;
    while (i < 3) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "loop_old_count_invariant.c";

int32 loop_old_count_invariant(int32 p[3]) {
    requires loadable(p[0..3]);
    ensures result_value: result == 3;
} by {
    step();
    step();
    loop {
        invariant i >= 0 and i <= 3;
        invariant old(count(p, 0, 3, p[0])) == old(count(p, 0, 3, p[0]));
        immutable by frame;
    }
    step();
    simp();
}
```

```expect
pass
```
