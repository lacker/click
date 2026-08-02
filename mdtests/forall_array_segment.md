# forall array segment is proved for unchanged memory

This checks that `auto` proves a quantified array-segment postcondition when the
function does not write through `p`.

```c filename=forall_array_segment.c
int32 forall_array_segment(int32 p[], int32 n) {
    return n;
}
```

```click
verifying "forall_array_segment.c";

int32 forall_array_segment(int32 p[], int32 n) {
    requires n >= 0 and n <= 3;
    requires loadable(p[0..3]);
    ensures segment_unchanged: forall (k: int32) {
        0 <= k and k < n implies p[k] == old(p[k])
    } by auto;
}
```

```expect
pass
```
