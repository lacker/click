# Constant narrowing at an argument wraps modulo 256

`-56` passed to an `unsigned char` parameter converts modulo 256, as GCC and
Clang do, and owes no range: `take` receives 200.
This test formerly pinned a refusal naming the range and value.

```c filename=constant_narrowing_argument_wraps_modulo_256.c
int take(unsigned char c) { return c; }
int f(void) { int x = -56; return take(x); }
```

```click
verifying "constant_narrowing_argument_wraps_modulo_256.c";
int32 take(uint8 c) { ensures result == c; } by { execute(); simp(); }
int32 f() { ensures result == 200; } by { execute(); simp(); }
```

```expect
pass
```
