# Substitution in `close() using` keeps the equality's offset

`y == x + 1` and `0 <= x` do not give `y <= x`, which is false for every `x`.
Substituting through the equality carries its `+ 1`, so the certificate
search finds no combination and the listed premises are refused.

```c filename=arithmetic_substitution_keeps_the_equality_offset.c
int32 next(int32 x, int32 y) {
    return 0;
}
```

```click
verifying "arithmetic_substitution_keeps_the_equality_offset.c";

int32 next(int32 x, int32 y) {
    requires x < 100;
    requires to_integer(y) == to_integer(x + 1);
    requires 0 <= x;
    ensures result == 0;
} by {
    have y <= x by { close() using { to_integer(y) == to_integer(x + 1); 0 <= x; }; }
    step();
    close();
}
```

```expect
fail: current goal does not follow from exactly the listed arithmetic premises
```
