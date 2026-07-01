# represented resource rejects duplicate contained token

This checks that a represented affine resource cannot contain the same named
affine token twice.

```c filename=zero.c
int32 zero(int32 fd) {
    return 0;
}
```

```click
affine resource socket_open(fd: int32);

affine resource bad_bundle(fd: int32) {
    contains socket_open(fd);
    contains socket_open(fd);
}

verifying "zero.c";

int32 zero(int32 fd) {
    requires bad_bundle(fd);
}
```

```expect
fail: duplicate affine resource `socket_open(fd)`
```
