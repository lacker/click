# Native views cover checked nonwrapping subranges

The offset and length remain complete unsigned 64-bit byte counts. Subtracting
the offset requires it to fit within the source range before its remaining
capacity can cover the requested view.

```c filename=window.c
void window(const unsigned char *p, unsigned long held, unsigned long start, unsigned long requested) {}
```

```click
target "x86_64-linux-userspace";
verifying "window.c";
void window(const uint8* p, uint64 held, uint64 start, uint64 requested) {
 requires start <= 9223372036854775807u64;
 requires start <= held;
 requires requested <= held - start;
 requires requested <= 9223372036854775807u64;
 views p[0u64..held];
 ensures viewable((p + start)[0u64..requested]);
} by {
 execute();
 simp() using { viewable(p[0u64..held]); start <= 9223372036854775807u64; start <= held; requested <= held - start; requested <= 9223372036854775807u64; };
}
```

```expect
pass
```
