# an unestablished conversion condition names which machine bound is missing

Converting a mathematical `Integer` back to `int32` requires both ends of the
`int32` range. A mathematical value has no reconstruction into source names, so
the refusal says which end of which range is missing, prints the converted value
in the verifier's own value names, and says that is what it is doing.

```click
theorem back_to_int32(n: Integer) {
    requires n >= 0;
    ensures to_int32(n + 1) == to_int32(n + 1) by { simp(); }
}
```

```expect
fail: not established: the Integer converted back to a machine type must fit it: its lower bound `-2147483648` is not established for the converted value, written here in the verifier's own Integer value names as `(i0+1)`
```
