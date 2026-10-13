# Native views support checked same-base prefixes

Counts remain unsigned 64-bit values. The symbolic prefix is not limited to
32-bit lengths, and wider element types compare their complete byte extents.

```c filename=native_prefix.c
void byte_prefix(const unsigned char *p, unsigned long held, unsigned long requested) {}
void word_prefix(const unsigned int *p, unsigned long held, unsigned long requested) {}
void first_byte(const unsigned char *p, unsigned long held) {}
```

```click
target "x86_64-linux-userspace";
verifying "native_prefix.c";
void byte_prefix(const uint8* p, uint64 held, uint64 requested) {
    requires requested <= held;
    views p[0u64..held];
    ensures viewable(p[0u64..requested]);
} by {
    apply(uint64_less_equal_transitive(requested, held, 9223372036854775807u64));
    execute();
    simp() using { requested <= held; viewable(p[0u64..held]); requested <= 9223372036854775807u64; };
}
void word_prefix(const uint32* p, uint64 held, uint64 requested) {
    requires held <= 2305843009213693951u64;
    requires requested <= held;
    requires requested * 4u64 <= held * 4u64;
    views p[0u64..held];
    ensures viewable(p[0u64..requested]);
} by {
    apply(uint64_less_equal_transitive(requested, held, 2305843009213693951u64));
    execute();
    simp() using { requested * 4u64 <= held * 4u64; viewable(p[0u64..held]); requested <= 2305843009213693951u64; };
}
void first_byte(const uint8* p, uint64 held) {
    requires 1u64 <= held;
    views p[0u64..held];
    ensures viewable(p[0u64..1u64]);
} by { execute(); simp() using { 1u64 <= held; viewable(p[0u64..held]); }; }
```

```expect
pass
```
