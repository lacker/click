# represented resource rejects resource fact read

This checks that a represented resource cannot claim a fact about memory
unless it contains write permission covering that memory.

```click
affine resource bogus(flag: int32*) {
    fact flag[0] == 0;
}
```

```expect
fail: resource `bogus` fact reads `flag[0]` without a covering contained `write(...)` resource
```
