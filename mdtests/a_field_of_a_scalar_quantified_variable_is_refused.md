# A scalar quantified variable has no fields

```c filename=scalar_field.c
void f(int32* p) { }
```

```click
verifying "scalar_field.c";

void f(int32* p) {
    requires true;
    ensures true;
} by {
    have forall (k: int32) { k.n == 5 } by { close(); }
}
```

```expect
fail: cannot read field `n` of `k`: `int32` has no fields
```
