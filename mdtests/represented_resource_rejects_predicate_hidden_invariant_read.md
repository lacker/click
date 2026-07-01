# represented resource rejects predicate-hidden invariant read

This checks that memory reads hidden behind a predicate still need to be backed
by contained write permission.

```click
predicate flag_is_zero(int32* flag) {
    flag[0] == 0
}

affine resource bogus(flag: int32*) {
    invariant flag_is_zero(flag);
}
```

```expect
fail: resource `bogus` invariant reads `flag[0]` without a covering contained `write(...)` resource
```
