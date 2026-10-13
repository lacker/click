# A return narrowing in range verifies

The in-range companion of
`mdtests/an_out_of_range_return_narrowing_wraps_modulo_256.md`: `x == 44`
puts the returned `int32` inside the `uint8` range, where the conversion is
the value itself. A fact that implies the range is enough; an exact
`x >= 0` and `x <= 255` is not required.

```c filename=a_return_narrowing_in_range_verifies.c
uint8 f(int32 x) { return x; }
```

```click
verifying "a_return_narrowing_in_range_verifies.c";

uint8 f(int32 x) {
    requires x == 44;
    ensures result == 44;
} by { execute(); simp(); }
```

```expect
pass
```
