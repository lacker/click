# Native view prefixes require full-width coverage at the same base

```c filename=native_prefix.c
void prefix(const unsigned char *p, const unsigned char *q, unsigned long held, unsigned long requested) {}
```

```click
target "x86_64-linux-userspace";
verifying "native_prefix.c";
void prefix(const uint8* p, const uint8* q, uint64 held, uint64 requested) {
    requires requested == held + 1u64;
    requires held <= 15u64;
    views p[0u64..held];
    ensures viewable(p[0u64..requested]);
} by { execute(); simp(); }
```

```expect
fail: unclosed goal
```
