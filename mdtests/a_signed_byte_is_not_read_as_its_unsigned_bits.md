# A signed byte is not read as its unsigned bits

The byte `0xff` stored as a `signed char` promotes to `-1`. A claim that reads
it as the unsigned `255` is refused.

```c filename=signed_byte_bits.c
int minus_one(void) { signed char x = -1; return x; }
```

```click
verifying "signed_byte_bits.c";

int minus_one() { ensures result == 255 by auto; }
```

```expect
fail: left side evaluated to -1, right side evaluated to 255
```
