# A native window needs complete nonwrapping coverage

```c filename=window.c
void window(const unsigned char *p, unsigned long held, unsigned long start, unsigned long requested) {}
```

```click
target "x86_64-linux-userspace";
verifying "window.c";
void window(const uint8* p, uint64 held, uint64 start, uint64 requested) {
    requires held == 16u64;
    requires start == 1u64;
    requires requested == 16u64;
    views p[0u64..held];
    ensures viewable((p + start)[0u64..requested]);
} by { execute(); simp(); }
```

```expect
fail: unclosed goal
```
