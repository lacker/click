# composite resource rejects resource fact read

This checks that memory reads hidden behind a predicate still need to be backed
by contained write permission.

```click
predicate flag_is_zero(flag: int32*) {
    flag[0] == 0
}

resource bogus(flag: int32*) {
    fact flag_is_zero(flag);
}
```

```expect
fail: resource `bogus` fact reads `flag[0]` without a covering contained owned memory resource
```
