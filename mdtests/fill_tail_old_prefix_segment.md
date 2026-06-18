# fill_tail proves an old-value prefix

This checks that a memory-changing loop can prove an old-memory postcondition
when that unchanged-memory fact is stated as an explicit quantified invariant.
The prefix is outside the mutated suffix.

```c filename=fill_tail_old_prefix_segment.c
int32 fill_tail_old_prefix_segment(int32 p[], int32 n) {
    int32 i;
    i = 1;
    while (i < n) {
        p[i] = i;
        i = i + 1;
    }
    return n;
}
```

```click
verifying "fill_tail_old_prefix_segment.c";

int32 fill_tail_old_prefix_segment(int32 p[], int32 n) {
    requires n >= 1 and n <= 2147483647;
    requires valid_range(p[0..n]);
    loop 0 {
        invariant i >= 1 and i <= n by auto;
        invariant forall (int32 k) {
            0 <= k and k < 1 implies p[k] == old(p[k])
        } by auto;
    }
    ensures prefix_unchanged: forall (int32 k) {
        0 <= k and k < 1 implies p[k] == old(p[k])
    } by auto;
}
```

```expect
pass
```
