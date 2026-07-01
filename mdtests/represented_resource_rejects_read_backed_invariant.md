# represented resource rejects read-backed invariant

This checks that a read permission is not enough to stabilize a represented
resource invariant. The resource must own write permission for memory that the
invariant reads.

```click
affine resource bogus(flag: int32*) {
    contains read(flag[0..1]);
    invariant flag[0] == 0;
}
```

```expect
fail: resource `bogus` invariant reads `flag[0]` without a covering contained `write(...)` resource
```
