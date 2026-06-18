# pointer parameters may alias without disjoint

Different pointer parameters are modeled like C pointers: they can refer to
overlapping memory unless the contract says otherwise. This test intentionally
omits `disjoint(dst[0..1], src[0..1])`, so Click must reject the claim that a
write through `dst` preserves `src[0]`.

```c filename=pointer_params_may_alias_without_disjoint.c
int32 clobber_dst(int32* dst, int32* src) {
    dst[0] = 1;
    return src[0];
}
```

```click
verifying "pointer_params_may_alias_without_disjoint.c";

int32 clobber_dst(int32* dst, int32* src) {
    requires valid_range(dst[0..1]);
    requires valid_range(src[0..1]);

    ensures source_unchanged: src[0] == old(src[0]) by auto;
}
```

```expect
fail: clobber_dst.source_unchanged
```
