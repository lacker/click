# A left conjunct cannot hide a right side that is undefined wherever it is read

The right side of `and` is read only where the left side is true. Here that
is `s >= 64u64`, where `1u64 << s` shifts by the width or more and has no
value, so the requirement is refused where it is declared.

```click
theorem guarded(s: uint64) {
    requires s >= 64u64 and (1u64 << s) == 2u64;
    ensures 1 == 1 by close();
}
```

```expect
fail: not established: `s >= 64u64 implies not s >= 64u64`
```
