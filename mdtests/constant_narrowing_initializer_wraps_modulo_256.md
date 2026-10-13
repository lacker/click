# Constant narrowing at an initializer wraps modulo 256

Initializing an `unsigned char` from a local holding `-56` stores 200, as
GCC and Clang do; no range is owed.
This test formerly pinned a refusal naming the range and value.

```c filename=constant_narrowing_initializer_wraps_modulo_256.c
int f(void) { int x = -56; unsigned char c = x; return c; }
```

```click
verifying "constant_narrowing_initializer_wraps_modulo_256.c";
int32 f() { ensures result == 200; } by { execute(); simp(); }
```

```expect
pass
```
