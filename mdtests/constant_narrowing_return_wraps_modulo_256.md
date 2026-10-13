# Constant narrowing at a return wraps modulo 256

Returning a local holding `-56` from an `unsigned char` function returns
200, as GCC and Clang do; no range is owed.
This test formerly pinned a refusal naming the range and value.

```c filename=constant_narrowing_return_wraps_modulo_256.c
unsigned char f(void) { int x = -56; return x; }
```

```click
verifying "constant_narrowing_return_wraps_modulo_256.c";
uint8 f() { ensures result == 200; } by { execute(); simp(); }
```

```expect
pass
```
