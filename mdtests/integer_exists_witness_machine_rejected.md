# Integer witnesses cannot use a machine carrier

```click
theorem integer_exists_witness_machine(c: int32) {
    ensures exists (z: Integer) { z == 0 } by {
        witness(z = c);
    }
}
```

```expect
fail: witness must be an Integer expression
```
