# `old(n)` is not the current `n`

The companion of `old_reads_a_reassigned_parameter_at_entry.md`: after
`n = n - 1` the current `n` is zero, and a proof that claims `old(n)` is zero
is refused. It used to verify.

```c filename=old_rejects_the_current_value_of_a_reassigned_parameter.c
int32 dec(int32 n) {
    n = n - 1;
    return n;
}
```

```click
verifying "old_rejects_the_current_value_of_a_reassigned_parameter.c";

int32 dec(int32 n) {
    requires n == 1;
    ensures result == 0;
} by {
    step();
    have old(n) == 0 by { simp(); }
    step();
    simp();
}
```

```expect
fail: `have` failed for `old(n) == 0`
```
