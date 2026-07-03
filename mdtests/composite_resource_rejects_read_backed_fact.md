# composite resource rejects read-backed fact

This checks that a read permission is not enough to stabilize a composite
resource fact. The resource must own write permission for memory that the
fact reads.

```click
resource bogus(flag: int32*) {
    contains read(flag[0..1]);
    fact flag[0] == 0;
}
```

```expect
fail: resource `bogus` fact reads `flag[0]` without a covering contained `write(...)` resource
note: contained resource coverage considered:
  - `read(flag[0..1])` is not a `write(...)` resource
```
