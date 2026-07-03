# composite resource rejects duplicate contained token

This checks that a composite resource cannot contain the same named
resource token twice.

```c filename=zero.c
int32 zero(int32 fd) {
    return 0;
}
```

```click
resource socket_open(fd: int32);

resource bad_bundle(fd: int32) {
    contains socket_open(fd);
    contains socket_open(fd);
}

verifying "zero.c";

int32 zero(int32 fd) {
    requires bad_bundle(fd);
}
```

```expect
fail: duplicate resource `socket_open(fd)`
```
