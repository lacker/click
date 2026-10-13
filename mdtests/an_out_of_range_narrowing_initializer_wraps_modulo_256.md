# An out-of-range narrowing initializer wraps modulo 256

`uint8 y = x` converts `x` to `uint8` as GCC and Clang do: modulo 256, with
no range owed. With `x == 300` the initializer stores 44, and the function
returns it. This test formerly pinned a refusal that named the range and the
value; the conversion now has the value C gives it.
`mdtests/an_out_of_range_return_narrowing_wraps_modulo_256.md` is the same
conversion at a `return`.

```c filename=an_out_of_range_narrowing_initializer_wraps_modulo_256.c
int32 f(int32 x) { uint8 y = x; return y; }
```

```click
verifying "an_out_of_range_narrowing_initializer_wraps_modulo_256.c";

int32 f(int32 x) {
    requires x == 300;
    ensures result == 44;
} by { execute(); simp(); }
```

```expect
pass
```
