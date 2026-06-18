# shifted copy effect uses covering disjoint facts

This checks that a shifted loop effect summary can use a broader disjoint
requirement. The loop only mutates `dst[1..n]`, stated as
`(dst + 1)[0..n - 1]`, while the requirement states that the whole
`dst[0..n]` range is disjoint from `src[0..n]`.

```c filename=shifted_copy_effect_uses_covering_disjoint.c
int32 shifted_copy_effect_uses_covering_disjoint(int32 dst[], int32 src[], int32 n) {
    int32 i;
    i = 1;
    while (i < n) {
        dst[i] = src[i];
        i = i + 1;
    }
    return i;
}
```

```click
verifying "shifted_copy_effect_uses_covering_disjoint.c";

int32 shifted_copy_effect_uses_covering_disjoint(int32 dst[], int32 src[], int32 n) {
    requires n >= 1;
    requires n <= 2147483647;
    requires valid_range(dst[0..n]);
    requires valid_range(src[0..n]);
    requires disjoint(dst[0..n], src[0..n]);
    loop 0 {
        invariant i >= 1;
        invariant i <= n;
        mutable (dst + 1)[0..n - 1] by frame;
    }
    ensures source_unchanged: forall (int32 k) {
        0 <= k and k < n implies src[k] == old(src[k])
    };
    ensures returns_n: result == n;
}
```

```expect
pass
```
