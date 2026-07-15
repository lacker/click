# declared resources require resource verbs for output

`ensures` is reserved for pure facts. A declared resource output must use an
explicit resource verb.

```click
resource open_fd(fd: int32);

verifying "identity.c";

int32 identity(int32 fd) {
    ensures open_fd(fd) by auto;
}
```

```c filename=identity.c
int32 identity(int32 fd) {
    return fd;
}
```

```expect
fail: `ensures` accepts pure propositions only; use `owns open_fd(...)` or `produces open_fd(...)`
```
