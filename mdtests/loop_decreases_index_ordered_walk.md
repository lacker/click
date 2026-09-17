# a walk down index-ordered links terminates

Each entry of `next` names a strictly smaller index, so the links form a DAG
ordered by position and the walk's own cursor is a ranking measure. Nothing
about the loop's shape says so: the descent comes from a quantified fact about
memory, instantiated at the cursor before the step that follows the link.

```c filename=loop_decreases_index_ordered_walk.c
int32 walk(int32 next[8], int32 start) {
    int32 cur;
    cur = start;
    while (cur > 0) {
        cur = next[cur];
    }
    return cur;
}
```

```click
verifying "loop_decreases_index_ordered_walk.c";

int32 walk(int32 next[8], int32 start) {
    requires 0 <= start and start < 8;
    views next[0..8];
    requires forall (k: int32) {
        0 < k and k < 8 implies 0 <= next[k] and next[k] < k
    };
    ensures result == 0;
} by {
    step();
    step();
    loop {
        decreases cur;
        invariant 0 <= cur and cur < 8;
        initialize by simp;
        preserve by {
            have 0 < cur by simp;
            have 0 <= next[cur] and next[cur] < cur by {
                instantiate(forall (k: int32) {
                    0 < k and k < 8 implies 0 <= next[k] and next[k] < k
                }, cur) using { 0 < cur; cur < 8; }
                assumption();
            }
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
