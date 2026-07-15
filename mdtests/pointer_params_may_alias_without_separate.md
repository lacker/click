# pointer parameters may alias without separate

Different pointer parameters are modeled like C pointers: they can refer to
overlapping memory unless the contract says otherwise. This test intentionally
omits `separate(memory(dst[0..1]), memory(src[0..1]))`, so Click must reject the claim that a
write through `dst` preserves `src[0]`.

```c filename=pointer_params_may_alias_without_separate.c
int32 clobber_dst(int32* dst, int32* src) {
    dst[0] = 1;
    return src[0];
}
```

```click
verifying "pointer_params_may_alias_without_separate.c";

int32 clobber_dst(int32* dst, int32* src) {
    requires loadable(dst[0..1]);
    requires loadable(src[0..1]);
    consumes dst[0..1];
    views src[0..1];

    ensures source_unchanged: src[0] == old(src[0]) by auto;
}
```

```expect
fail: clobber_dst.source_unchanged
```
