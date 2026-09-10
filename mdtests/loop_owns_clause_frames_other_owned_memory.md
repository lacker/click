# A loop `owns` clause frames the function's other owned memory

The function owns both `p[0..n]` and `q[0..1]`, so the default loop footprint
would be both. The loop declares `owns p[0..n]`, which is the only memory its
body writes, so `q[0]` keeps its pre-loop value across the loop with no
invariant naming `q`.

```c filename=loop_owns_clause_frames_other_owned_memory.c
void loop_owns_clause_frames_other_owned_memory(int32 p[], int32 q[], int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        p[i] = i;
        i = i + 1;
    }
}
```

```click
verifying "loop_owns_clause_frames_other_owned_memory.c";

void loop_owns_clause_frames_other_owned_memory(int32 p[], int32 q[], int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    requires loadable(p[0..n]);
    requires loadable(q[0..1]);
    owns p[0..n];
    owns q[0..1];
    requires separate(memory(p[0..n]), memory(q[0..1]));
    ensures q_preserved: q[0] == old(q[0]);
} by {
    step();
    step();
    loop {
        owns p[0..n];
        invariant i >= 0;
        invariant i <= n;
    }
    step();
    simp();
}
```

```expect
pass
```
