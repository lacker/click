# an unestablished conversion condition names which machine bound is missing

Converting a mathematical `Integer` back to `int32` requires both ends of the
`int32` range. The premise proves the lower bound; the missing upper bound
still rejects the claim. The refusal names that bound and spells the converted
value with the theorem's own `Integer` binder, `n + 1`.

```click
theorem back_to_int32(n: Integer) {
    requires n >= 0;
    ensures to_int32(n + 1) == to_int32(n + 1) by close();
}
```

```expect
fail: not established: the Integer converted back to a machine type must fit it: its upper bound `2147483647` is not established for the converted value: `n + 1`
```
