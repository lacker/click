# A native witness carries its conversion domain

The selected witness must satisfy the conversion's range requirement and
its claimed value together.

```click quick-solve
theorem native_witness_conversion() {
    ensures exists (k: int32) {
        k == 255 and to_uint8(to_integer(k)) == to_uint8(to_integer(k))
    } by {
        witness(255);
        close();
    }
}
```

```expect
pass
```
