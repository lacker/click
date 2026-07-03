# represented resource packed nested fact projection

This checks that holding a packed represented resource exposes facts from
nested represented resources without an explicit `observe(...)` step.

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
pass
```
