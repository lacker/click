# a bare library name needs a path or a selective import

Library names are not in scope bare, even from an implicit module: `append`
here is not `list::append`.

```click
theorem append_nil_by_bare_name(xs: List<int32>) {
    ensures append(List<int32>::Nil, xs) == xs by close();
}
```

```expect
fail: append
```
