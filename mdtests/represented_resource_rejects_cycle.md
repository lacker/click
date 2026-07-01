# represented resource rejects cycles

This checks that represented resource definitions cannot recursively contain
each other.

```c filename=zero.c
int32 zero(int32 fd) {
    return 0;
}
```

```click
affine resource left_token(fd: int32) {
    contains right_token(fd);
}

affine resource right_token(fd: int32) {
    contains left_token(fd);
}

verifying "zero.c";

int32 zero(int32 fd) {
    requires left_token(fd);
}
```

```expect
fail: resource representation cycle
```
