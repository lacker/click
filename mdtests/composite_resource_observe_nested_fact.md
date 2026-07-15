# composite resource observe nested fact

This checks that `observe(resource)` takes one view step. Observing the outer
resource exposes a view of the contained composite resource; observing that
contained resource exposes its fact, without unfolding either resource.

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
    consumes live_fd(fd);

    ensures result >= 0 by {
        observe(live_fd(fd));
        observe(nonnegative_fd(fd));
        symbolic_execute();
        simp();
    }

    produces live_fd(fd) by auto;
}
```

```expect
pass
```
