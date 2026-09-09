# C integer expressions use the modeled ABI types

The three functions cover decimal negative-literal typing, LP64 `sizeof`,
and the conditional operator's usual arithmetic conversions.

```c filename=negative.c
int32 negated_literal() {
    return -2147483648 < 0u;
}
```

```c filename=sizeof.c
int32 sizeof_cmp() {
    return sizeof(int32) - 5 < 0;
}
```

```c filename=conditional.c
int32 conditional_cmp() {
    return (1 ? -1 : 1u) < 0;
}
```

```c filename=wide_division.c
long wide_division() {
    return -2147483648 / -1;
}
```

```click
verifying "negative.c";
verifying "sizeof.c";
verifying "conditional.c";
verifying "wide_division.c";

int32 negated_literal() {
    ensures result == 1;
}

int32 sizeof_cmp() {
    ensures result == 0;
}

int32 conditional_cmp() {
    ensures result == 0;
}

long wide_division() {
    ensures result == 2147483648;
}
```

```expect
pass
```
