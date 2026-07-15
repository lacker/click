# resource can be borrowed and returned

This checks the first user-defined resource slice. `open_fd(fd)` is a token
resource carried in the resource context. The helper requires it and
returns it, so the caller can use the same token twice and still prove it has
the token.

```c filename=borrow_fd.c
int32 borrow_fd(int32 fd) {
    return fd;
}
```

```c filename=borrow_fd_twice.c
int32 borrow_fd_twice(int32 fd) {
    int32 value;
    value = borrow_fd(fd);
    value = borrow_fd(fd);
    return value;
}
```

```click
resource open_fd(fd: int32);

verifying "borrow_fd.c";
verifying "borrow_fd_twice.c";

int32 borrow_fd(int32 fd) {
    consumes open_fd(fd);

    produces open_fd(fd) by auto;
}

int32 borrow_fd_twice(int32 fd) {
    consumes open_fd(fd);

    produces open_fd(fd) by auto;
}
```

```expect
pass
```
