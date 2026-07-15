# resource consumed by call

This checks that a token resource is consumed when a callee requires it
and does not return it. `close_fd(fd)` receives `open_fd(fd)` but has no
matching resource `ensures`, so the later `borrow_fd(fd)` call fails.

```c filename=borrow_fd.c
int32 borrow_fd(int32 fd) {
    return fd;
}
```

```c filename=close_fd.c
int32 close_fd(int32 fd) {
    return 0;
}
```

```c filename=borrow_after_close.c
int32 borrow_after_close(int32 fd) {
    int32 value;
    value = close_fd(fd);
    value = borrow_fd(fd);
    return value;
}
```

```click
resource open_fd(fd: int32);

verifying "borrow_fd.c";
verifying "close_fd.c";
verifying "borrow_after_close.c";

int32 borrow_fd(int32 fd) {
    consumes open_fd(fd);

    produces open_fd(fd) by auto;
}

int32 close_fd(int32 fd) {
    consumes open_fd(fd);

    ensures result == 0 by auto;
}

int32 borrow_after_close(int32 fd) {
    consumes open_fd(fd);

    ensures result == fd by auto;
}
```

```expect
fail: missing resource fact `owns open_fd(fd)`
```
