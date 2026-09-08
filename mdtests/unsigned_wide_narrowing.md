# Unsigned 64-to-32-bit conversions are truncations, not equalities

```c filename=narrow.c
unsigned int implicit(unsigned long x) { unsigned int y = x; return y; }
unsigned int explicit(unsigned long x) { return (unsigned int)x; }
unsigned int signed_input(long x) { return x; }
unsigned int top_five(unsigned long x) { unsigned int y = x >> 59; return 1u << y; }
unsigned int constant(void) { return 4294967303ULL; }
unsigned int echo(unsigned int n) { return n; }
unsigned int argument(unsigned long x) { return echo(x); }
```

```click
verifying "narrow.c";
unsigned int implicit(unsigned long x) {
    ensures result == (uint32)x;
} by { execute(); simp(); }
unsigned int explicit(unsigned long x) {
    ensures result == (uint32)x;
} by { execute(); simp(); }
unsigned int signed_input(long x) {
    ensures result == (uint32)x;
} by { execute(); simp(); }
unsigned int top_five(unsigned long x) {
    ensures result == (1u32 << (uint32)(x >> 59));
} by { execute(); simp(); }
unsigned int constant() {
    ensures result == 7u32;
} by { execute(); simp(); }
unsigned int echo(unsigned int n) {
    ensures result == n;
} by { execute(); simp(); }
unsigned int argument(unsigned long x) {
    ensures result == (uint32)x;
} by { execute(); simp(); }
```

```expect
pass
```
