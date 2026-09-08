# Signed 64-bit compound updates still reject overflow

```c filename=overflow.c
long overflow(void) { long x = 9223372036854775807LL; x += 1; return x; }
```

```click
verifying "overflow.c";
long overflow() { ensures result == result; } by { execute(); simp(); }
```

```expect
fail: undefined behavior: signed overflow
```
