# shifted copy effect uses covering separate facts

This checks that a shifted loop effect summary can use a broader separation
requirement. The loop only mutates `dst[1..n]`, stated as
`(dst + 1)[0..n - 1]`, while the requirement states that the whole
`dst[0..n]` range is separate from `src[0..n]`.

```c filename=shifted_copy_effect_uses_covering_separate.c
int32 shifted_copy_effect_uses_covering_separate(int32 dst[], int32 src[], int32 n) {
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
verifying "shifted_copy_effect_uses_covering_separate.c";

int32 shifted_copy_effect_uses_covering_separate(int32 dst[], int32 src[], int32 n) {
    requires n >= 1;
    requires n <= 2147483647;
    requires loadable(dst[0..n]);
    requires loadable(src[0..n]);
    consumes dst[0..n];
    views src[0..n];
    requires separate(memory(dst[0..n]), memory(src[0..n]));
    ensures source_unchanged: forall (k: int32) {
        0 <= k and k < n implies src[k] == old(src[k])
    };
    ensures returns_n: result == n;
} by {
    step();
    step();
    loop {
        invariant i >= 1;
        invariant i <= n;
        mutable (dst + 1)[0..n - 1] by frame;
    }
    step();
    simp();
}
```

```expect
pass
```
