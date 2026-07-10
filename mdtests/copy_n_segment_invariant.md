# copy_n proves a symbolic copied segment

This checks that a symbolic pointer-copy loop can prove a quantified copied
segment. The destination prefix invariant says what has been copied so far; the
whole-loop mutable clause plus the disjoint source/destination requirement lets
the prover derive that the source segment still equals its function-entry
contents.

```c filename=copy_n_segment_invariant.c
int32 copy_n_segment_invariant(int32 dst[], int32 src[], int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        dst[i] = src[i];
        i = i + 1;
    }
    return i;
}
```

```click
verifying "copy_n_segment_invariant.c";

int32 copy_n_segment_invariant(int32 dst[], int32 src[], int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    requires loadable(dst[0..n]);
    requires loadable(src[0..n]);
    requires write(dst[0..n]);
    requires read(src[0..n]);
    requires disjoint(dst[0..n], src[0..n]);
    for loop(0) {
        invariant i >= 0 by auto;
        invariant i <= n by auto;
        invariant forall (int32 k) {
            0 <= k and k < i implies dst[k] == old(src[k])
        } by auto;
        mutable dst[0..n] by frame;
    }
    ensures returns_n: result == n by auto;
    ensures source_unchanged: forall (int32 k) {
        0 <= k and k < n implies src[k] == old(src[k])
    } by auto;
    ensures copied_segment: forall (int32 k) {
        0 <= k and k < n implies dst[k] == old(src[k])
    } by auto;
}
```

```expect
pass
```
