# `solve` does not supply a conjunct a guarded universal lacks

Dropping conjuncts of a guarded universal yields only the conjuncts it
states. A requirement that every byte is defined says nothing about the
bytes' values, so it does not supply `dst[k] == 7` for any `k`.

```c filename=keep.c
void keep(unsigned char *dst) {
}
```

```click
verifying "keep.c";

void keep(uint8* dst) {
    owns dst[0..4];
    requires (0u64..4u64).all(|k| { defined(dst[k]) });
    ensures (0u64..4u64).all(|k| { dst[k] == 7u8 });
} by {
    step_until(function.exit);
    close();
    close();
}
```

```expect
fail: `close` search did not retain a complete proof
```
