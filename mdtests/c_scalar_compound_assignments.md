# C scalar compound assignments

The remaining arithmetic, shift, and bitwise compound assignments lower to
the corresponding existing C0 expressions. They remain statement-only updates
on plain scalar locals.

```c filename=scalar_compound_assignments.c
int32 scalar_compound_assignments() {
    int32 value = 255;
    value /= 3;
    value %= 10;
    value <<= 1;
    value >>= 1;
    value &= 3;
    value |= 4;
    return value;
}
```

```click
verifying "scalar_compound_assignments.c";

int32 scalar_compound_assignments() {
    ensures result == 5 by auto;
}
```

```expect
pass
```
