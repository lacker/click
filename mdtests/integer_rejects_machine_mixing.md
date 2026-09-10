# mathematical Integer rejects machine scalar mixing

```click
theorem integer_rejects_machine_mixing(x: Integer) {
    ensures x == 1u32;
}
```

```expect
fail: mathematical Integer expressions cannot be compared with C values
```
