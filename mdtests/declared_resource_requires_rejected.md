# declared resources require resource verbs

`requires` is reserved for pure facts. A declared resource must use an explicit
resource verb.

```click
abstract resource open_fd(fd: int32);

verifying "identity.c";

int32 identity(int32 fd) {
    requires open_fd(fd);
    ensures result == fd by auto;
}
```

```c filename=identity.c
int32 identity(int32 fd) {
    return fd;
}
```

```expect
fail: `requires` accepts pure propositions only; use `owns open_fd(...)`, `views open_fd(...)`, or `consumes open_fd(...)`
```
