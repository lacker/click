# composite resource packed pure fact projection

This checks that holding a packed composite resource exposes its pure facts
without an explicit `unpack(...)` proof step.

```c filename=return_fd.c
int32 return_fd(int32 fd) {
    return fd;
}
```

```click
resource nonnegative_fd(fd: int32) {
    fact fd >= 0;
}

verifying "return_fd.c";

int32 return_fd(int32 fd) {
    requires nonnegative_fd(fd);

    ensures result >= 0 by auto;
    ensures nonnegative_fd(fd) by auto;
}
```

```expect
pass
```
