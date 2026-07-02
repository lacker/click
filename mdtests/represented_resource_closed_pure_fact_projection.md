# represented resource closed pure fact projection

This checks that holding a closed represented resource exposes its pure facts
without an explicit `open(...)` proof step.

```c filename=return_fd.c
int32 return_fd(int32 fd) {
    return fd;
}
```

```click
affine resource nonnegative_fd(fd: int32) {
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
