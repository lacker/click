# Signed 64-bit overflow

Signed 64-bit addition retains C's overflow undefined behavior.

```c filename=int64_signed_overflow.c
int64_t int64_signed_overflow() {
    return 9223372036854775807LL + 1LL;
}
```

```click
verifying "int64_signed_overflow.c";

int64_t int64_signed_overflow() {
    ensures no_result: result == 0 by auto;
}
```

```expect
fail: undefined behavior: signed overflow
```
