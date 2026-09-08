# a sidecar literal takes the type it takes in a C source

An unsuffixed decimal literal in a sidecar is typed the way the C frontend
types the same spelling: `int32` while it fits, then the wider integer types.
Reading a literal above `INT32_MAX` as that bit pattern in a signed `int32`
would make `4294967295` denote -1 and compare equal to it.

`int32` reaches one further below zero than above it, so `-2147483648` is
still `INT32_MIN`; the magnitude narrows under the minus sign that consumes
it, not on its own.

```c filename=sidecar_literal_types_match_c.c
int32 minus_one() {
    return -1;
}

int32 int_minimum() {
    return -2147483648;
}

int64 above_uint32() {
    return 4294967296;
}

uint64 all_ones() {
    return 0xFFFFFFFFFFFFFFFF;
}
```

```click
verifying "sidecar_literal_types_match_c.c";

int32 minus_one() {
    ensures result == -1 by auto;
}

int32 int_minimum() {
    ensures result == -2147483648 by auto;
}

int64 above_uint32() {
    ensures result == 4294967296 by auto;
}

uint64 all_ones() {
    ensures result == 18446744073709551615 by auto;
}
```

```expect
pass
```
