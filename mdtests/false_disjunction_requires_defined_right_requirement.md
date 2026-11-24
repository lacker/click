# A false left disjunct cannot hide an undefined shift on the right

The right side of `or` is read only where the left side is false. Here that
is `s >= 64u64`, where `1u64 << s` shifts by the width or more and has no
value, so the requirement is refused where it is declared.

```click
theorem guarded(s: uint64) {
    requires s < 64u64 or (1u64 << s) == 2u64;
    ensures 1 == 1 by close();
}

theorem invalid_wide_instance() {
    ensures 1 == 1 by apply(guarded(64u64));
}
```

```expect
fail: not established: `s < 64u64 or not s >= 64u64`
```
