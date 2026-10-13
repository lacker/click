# A sidecar conjunction written `&&` is told to use `and`

Click writes conjunction as `and` and disjunction as `or`. A sidecar that
writes C's `&&` gets that spelling rather than a complaint about a bitwise
`&` operand.

```c filename=a_sidecar_conjunction_written_as_ampersands_names_and.c
int product(int u, int v) { return u * v; }
```

```click
verifying "a_sidecar_conjunction_written_as_ampersands_names_and.c";

int32 product(int32 u, int32 v) {
    requires u < 100 && v < 100;
    ensures result == u * v by auto;
}
```

```expect
fail: Click writes conjunction as `and`, not `&&`
```
