# `rewrite` replaces only an occurrence of the parsed left side

`rewrite(L, R)` replaces subterms identical to `L` as lowered. C
arithmetic in Click associates to the left, so `x + y + w` is
`(x + y) + w`: it contains `x + y` but not `y + w`, and a rewrite by
`y + w == z` finds nothing to replace.

```click
theorem left_prefix_occurs(x: int32, y: int32, w: int32, z: int32) {
    requires x + y == z;
    ensures x + y + w == z + w by {
        rewrite(x + y, z);
        close();
    }
}

theorem right_suffix_does_not_occur(x: int32, y: int32, w: int32, z: int32) {
    requires y + w == z;
    ensures x + y + w == x + z by {
        rewrite(y + w, z);
        normalize();
    }
}
```

```expect
fail: `rewrite` equality does not occur in the current goal
```
