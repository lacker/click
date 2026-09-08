# Compound updates use the existing 64-bit arithmetic semantics

```c filename=updates.c
unsigned long unsigned_updates(void) {
    unsigned long x = 18446744073709551615ULL;
    x += 3; x -= 2; x *= 5; x /= 3; x %= 7;
    x <<= 2; x >>= 1; x ^= 3; x |= 8; x &= 15;
    return x;
}
long signed_updates(void) {
    long x = 10;
    x += 1; x -= 2; x *= 3; x /= 3; x %= 5;
    x <<= 1; x >>= 2; x ^= 3; x |= 8; x &= 15;
    return x;
}
```

```click
verifying "updates.c";
unsigned long unsigned_updates() {
    ensures result == 11u64;
} by { execute(); simp(); }
long signed_updates() {
    ensures result == 9i64;
} by { execute(); simp(); }
```

```expect
pass
```
