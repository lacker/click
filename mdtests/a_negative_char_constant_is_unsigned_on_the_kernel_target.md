# A negative `char` constant is unsigned on the kernel target

The x86_64-linux-kernel form of
`an_out_of_range_integer_constant_converts_modulo_its_destination_width.md`.
Plain `char` is unsigned there, as GCC's `-funsigned-char` makes it, so
`char c = -56` holds `200`, as does the argument `-56` passed to a `char`
parameter.

```c filename=a_negative_char_constant_is_unsigned_on_the_kernel_target.c
int initialize(void) {
    char c = -56;
    return c;
}

int widen(char c) { return c; }

int argument(void) { return widen(-1); }
```

```click
target "x86_64-linux-kernel";
verifying "a_negative_char_constant_is_unsigned_on_the_kernel_target.c";

int initialize() { ensures result == 200 by auto; }
int widen(char c) { ensures result == c by auto; }
int argument() { ensures result == 255 by auto; }
```

```expect
pass
```
