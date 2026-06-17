# forall array segment syntax is parsed but not proved yet

This documents the intended quantified proposition shape for array segments.
The function does not write through `p`, so the specification is plausible, but
`auto` does not yet prove quantified array-segment facts.

```c filename=forall_array_segment.c
int32 forall_array_segment(int32 p[], int32 n) {
    return n;
}
```

```click
verifying "forall_array_segment.c";

int32 forall_array_segment(int32 p[], int32 n) {
    requires n >= 0 and n <= 3;
    requires valid_range(p, 12);
    ensures segment_preserved: forall (int32 k) {
        0 <= k and k < n implies p[k] == old(p[k])
    } by auto;
}
```

```expect
fail: proposition was not provable
```
