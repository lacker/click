# represented resource allows pure invariant

This checks that a represented resource may carry scalar invariant facts that
do not read mutable memory.

```click
affine resource nonnegative_fd(fd: int32) {
    invariant fd >= 0;
}
```

```expect
pass
```
