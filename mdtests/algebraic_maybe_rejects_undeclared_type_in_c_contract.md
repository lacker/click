# C contracts cannot invent algebraic constructors

```c filename=algebraic_maybe_rejects_undeclared_type.c
int32 identity(int32 value) {
    return value;
}
```

```click
verifying "algebraic_maybe_rejects_undeclared_type.c";

int32 identity(int32 value) {
    ensures Phantom<int32>::Wrap(result) == Phantom<int32>::Wrap(value) by auto;
}
```

```expect
fail: unknown algebraic datatype `Phantom`
```
