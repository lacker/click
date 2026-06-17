# Click proposition logic

This checks Click proposition syntax in a sidecar proof. The logical words
`and`, `not`, and `implies` are Click syntax, distinct from C expression
operators.

```c filename=identity_prop.c
int32 identity_prop(int32 x) {
    return x;
}
```

```click
verifying "identity_prop.c";

int32 identity_prop(int32 x) {
    ensures prop_logic: result == x and not (result != x) by auto;
    ensures prop_implies: result == x implies result == x by auto;
}
```

```expect
pass
```
