# copy_n proves a symbolic copied segment

This checks that a symbolic pointer-copy loop can prove a quantified copied
segment. The destination prefix invariant says what has been copied so far; the
whole-loop mutable clause plus the separated source/destination requirement lets
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

theorem int32_le_antisymmetric(left: int32, right: int32) {
    requires left <= right;
    requires right <= left;
    ensures left == right;
}

int32 copy_n_segment_invariant(int32 dst[], int32 src[], int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    requires loadable(dst[0..n]);
    requires loadable(src[0..n]);
    consumes dst[0..n];
    views src[0..n];
    requires separate(memory(dst[0..n]), memory(src[0..n]));
    ensures returns_n: result == n;
    ensures source_unchanged: forall (k: int32) {
        0 <= k and k < n implies src[k] == old(src[k])
    };
    ensures copied_segment: forall (k: int32) {
        0 <= k and k < n implies dst[k] == old(src[k])
    };
} by {
    step();
    step();
    loop {
        invariant i >= 0;
        invariant i <= n;
        invariant forall (k: int32) {
            0 <= k and k < i implies dst[k] == old(src[k])
        };
        mutable dst[0..n] by frame;
    }
    step();
    apply(int32_le_antisymmetric(
        at(loop(0).exit, i),
        at(loop(0).exit, n)
    )) using {
        at(loop(0).exit, i) <= at(loop(0).exit, n);
        at(loop(0).exit, n) <= at(loop(0).exit, i);
    }
    have result == n by {
        simp() using {
            at(loop(0).exit, i) == at(loop(0).exit, n);
        }
    }
    have forall (k: int32) { 0 <= k and k < n implies src[k] == old(src[k]) } by {
        derive using {
            n >= 0;
            n <= 2147483647;
            at(statement(0).entry, loadable(dst[0..n]));
            at(statement(0).entry, loadable(src[0..n]));
            separate(memory(dst[0..n]), memory(src[0..n]));
            at(loop(0).exit, i) >= at(loop(0).exit, 0);
            at(loop(0).exit, i) <= at(loop(0).exit, n);
            not at(loop(0).exit, i) < at(loop(0).exit, n);
            forall (k: int32) { at(loop(0).exit, 0) <= at(loop(0).exit, k) and at(loop(0).exit, k) < at(loop(0).exit, i) implies at(loop(0).exit, dst[k]) == old(src[k]) };
            result == n;
        }
    }
    have forall (k: int32) { 0 <= k and k < n implies dst[k] == old(src[k]) } by {
        derive using {
            n >= 0;
            n <= 2147483647;
            at(statement(0).entry, loadable(dst[0..n]));
            at(statement(0).entry, loadable(src[0..n]));
            separate(memory(dst[0..n]), memory(src[0..n]));
            at(loop(0).exit, i) >= at(loop(0).exit, 0);
            at(loop(0).exit, i) <= at(loop(0).exit, n);
            not at(loop(0).exit, i) < at(loop(0).exit, n);
            forall (k: int32) { at(loop(0).exit, 0) <= at(loop(0).exit, k) and at(loop(0).exit, k) < at(loop(0).exit, i) implies at(loop(0).exit, dst[k]) == old(src[k]) };
            result == n;
            forall (k: int32) { 0 <= k and k < n implies src[k] == old(src[k]) };
        }
    }
    assumption();
    assumption();
    assumption();
}
```

```expect
pass
```
