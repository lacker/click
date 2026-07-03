# represented resource allows pure fact

This checks that a represented resource may carry scalar resource facts that
do not read mutable memory.

```click
resource nonnegative_fd(fd: int32) {
    fact fd >= 0;
}
```

```expect
pass
```
