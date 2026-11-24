# Float-cast branch prerequisites retain source names and exact bounds

```c filename=branch_float_cast.c
int32 positive(double d) {
    if ((int32) d > 0) {
        return 1;
    }
    return 0;
}
```

```click
verifying "branch_float_cast.c";

int32 positive(double d) {
    ensures result >= 0;
} by {
    branch { true => { step(); close(); } false => {} }
    step();
    close();
}
```

```expect
fail: `d > float64_from_bits(0xc1e0000000200000u64)`
```
