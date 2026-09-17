# a bare `instantiate` in `preserve` names its repair

`instantiate` adds a fact and executes nothing, so the preservation driver
does not run it between execution steps. The refusal used to name the tactic
and stop there, which left no way to tell a proof-shape limitation from a
false proposition. It now says which it is and names the `have` form that
[`loop_decreases_index_ordered_walk.md`](loop_decreases_index_ordered_walk.md)
uses for the same instantiation.

```c filename=loop_preserve_bare_instantiate.c
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
verifying "loop_preserve_bare_instantiate.c";

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
            instantiate(forall (k: int32) {
                0 < k and k < 8 implies 0 <= next[k] and next[k] < k
            }, cur) using { 0 < cur; cur < 8; }
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
fail: move the operation into `have proposition by { ... }`
```
