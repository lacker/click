# Composite bodies can contain multiple equal units

Repeated contained clauses package the corresponding resource quantity rather
than duplicating one unit.

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
    consumes bad_bundle(fd);
}
```

```expect
pass
```
