# composite resource folded nested fact needs observe

This checks that folded composite-resource fact projection is one step. Holding
`live_fd(fd)` exposes its immediate body, but does not recursively expose the
fact inside `nonnegative_fd(fd)` without an explicit `observe(...)` step.

```c filename=return_fd.c
int32 return_fd(int32 fd) {
    return fd;
}
```

```click
resource nonnegative_fd(fd: int32) {
    fact fd >= 0;
}

resource live_fd(fd: int32) {
    contains nonnegative_fd(fd);
}

verifying "return_fd.c";

int32 return_fd(int32 fd) {
    requires live_fd(fd);

    ensures result >= 0 by auto;
    ensures live_fd(fd) by auto;
}
```

```expect
fail: left side evaluated to fd
```
