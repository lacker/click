# A shift-count mask cannot be removed at the first invalid count

```click
theorem shift_count_mask(s: int32) {
    requires s >= 0;
    requires s <= 32;
    ensures (s & 31) == s by close();
}
```

```expect
fail: could not establish `(s & 31) == s`
```
