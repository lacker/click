# an unestablished conversion condition names which machine bound is missing

Converting a mathematical `Integer` back to `int32` requires both ends of the
`int32` range. The refusal says which end of which range is missing, and
spells the converted value with the theorem's own `Integer` binder, `n + 1`.

```click
theorem back_to_int32(n: Integer) {
    requires n >= 0;
    ensures to_int32(n + 1) == to_int32(n + 1) by simp;
}
```

```expect
fail: not established: the Integer converted back to a machine type must fit it: its lower bound `-2147483648` is not established for the converted value: `n + 1`
```
