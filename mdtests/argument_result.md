# argument-dependent result verification

This checks that an `ensures` clause can compare the return value to a symbolic
parameter, not just to an integer literal.

```c filename=identity.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "identity.c";

int32 identity(int32 x) {
    ensures returns_argument: result == x by auto;
}
```

```expect
pass
```

