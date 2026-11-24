# A widened unsigned sum cannot establish a smaller upper bound

The same operand bounds permit a sum of 4294967295. They cannot establish
an upper bound of 4294967294.

```c filename=widened_unsigned_sum_bounds.c
long add_byte(unsigned sum, unsigned char byte) {
    unsigned word = (unsigned)byte;
    long wide = (long)sum + (long)word;
    return wide;
}
```

```click
verifying "widened_unsigned_sum_bounds.c";
int64 add_byte(uint32 sum, uint8 byte) {
    requires sum <= 4294967040u32;
    ensures result <= 4294967294i64;
} by {
    step_until(function.exit);
    have result <= 4294967294i64 by {
        close() using { (byte as uint32) <= 255u32; sum <= 4294967040u32; };
    }
    close();
}
```

```expect
fail: could not prove
```
