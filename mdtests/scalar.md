# scalar expression verification

This checks that `auto` can prove a simple scalar result using Click's C integer
arithmetic and comparison semantics.

```c filename=scalar.c
int32 scalar() {
    return (1 + 2) == 3;
}
```

```click
verifying "scalar.c";

int32 scalar() {
    ensures arithmetic_result: result == 1 by auto;
}
```

```expect
pass
```
