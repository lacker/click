# A held byte range does not narrow past its end

`views a[0..n]` over `uint8` narrows to `viewable(a[0..k])` when
`0 <= k <= n` (`mdtests/loop_initialize_narrows_a_held_byte_range_under_a_universal.md`).
Without `k <= n`, `a[0..k]` may name bytes past the held range, which nothing
here makes loadable, and narrowing refuses it.

```c filename=a_held_byte_range_does_not_narrow_past_its_end.c
int32 first(uint8 *a, int32 n, int32 k) {
    return 0;
}
```

```click
verifying "a_held_byte_range_does_not_narrow_past_its_end.c";

int32 first(uint8 *a, int32 n, int32 k) {
    views a[0..n];
    requires 0 <= k;
    ensures result == 0;
} by {
    have viewable(a[0..k]) by { simp(); }
    step();
    simp();
}
```

```expect
fail: `viewable(a[0..k])` was not proved
```
