# Bitwise divisors use operand bounds to exclude zero and minus one

```c filename=arithmetic.c
int32 signed_or(int32 n, int32 a, int32 b) { return n / (a | b); }
uint32 unsigned_or(uint32 n, uint32 a, uint32 b) { return n / (a | b); }
int32 signed_xor(int32 n, int32 d) { return n / (d ^ 1); }
int64 signed_xor_wide(int64 n, int64 d) { return n % (d ^ 1LL); }
```

```click
verifying "arithmetic.c";

int32 signed_or(int32 n, int32 a, int32 b) { requires a > 0; requires b >= 0; ensures true; }
uint32 unsigned_or(uint32 n, uint32 a, uint32 b) { requires a != 0; ensures true; }
int32 signed_xor(int32 n, int32 d) { requires d >= 0; requires d != 1; ensures true; }
int64 signed_xor_wide(int64 n, int64 d) { requires d >= 0; requires d != 1; ensures true; }

theorem or_nonzero(a: int32, b: int32) {
    requires a > 0;
    ensures (a | b) != 0 by { close(); }
}
theorem xor_excludes_minus_one(d: int32) {
    requires d >= 0;
    ensures (d ^ 1) != -1 by { close(); }
}
```

```expect
pass
```
