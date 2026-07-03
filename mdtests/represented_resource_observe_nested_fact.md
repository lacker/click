# represented resource observe nested fact

This checks that `observe(resource)` exposes facts from represented resources
contained inside the observed packed resource, without unpacking either token.

```c filename=return_fd.c
int32 return_fd(int32 fd) {
    return fd;
}
```

```click
affine resource nonnegative_fd(fd: int32) {
    fact fd >= 0;
}

affine resource live_fd(fd: int32) {
    contains nonnegative_fd(fd);
}

verifying "return_fd.c";

int32 return_fd(int32 fd) {
    requires live_fd(fd);

    ensures result >= 0 by {
        observe(live_fd(fd));
        symbolic_execute();
        simp();
    }

    ensures live_fd(fd) by auto;
}
```

```expect
pass
```
