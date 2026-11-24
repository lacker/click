# A safe witness elsewhere cannot justify an out-of-range conversion

Zero is a valid input to `to_uint8`, but it cannot discharge the domain of
the selected witness 256. The conversion and the claim use the same witness.

```click
theorem native_witness_conversion() {
    ensures exists (k: int32) {
        k == 256 and to_uint8(to_integer(k)) == to_uint8(to_integer(k))
    } by {
        witness(256);
        close();
    }
}
```

```expect
fail: solve
```
