# represented resource rejects unowned invariant read

This checks that a represented resource cannot claim an invariant about memory
unless it contains write permission covering that memory.

```click
affine resource bogus(flag: int32*) {
    invariant flag[0] == 0;
}
```

```expect
fail: resource `bogus` invariant reads `flag[0]` without a covering contained `write(...)` resource
```
