# an unfolded range `all` does not capture a same-named argument

`mdtests/an_unfolded_quantifier_does_not_capture_a_same_named_argument.md`
through `(0..n).all(|j| ...)`, which lowers to the same `ForAllInt32` with
the written item name; the C parameter `j` substituted for `n` must keep
naming the parameter.

```c filename=repro.c
int32 f(int32 p[2], int32 j) {
    return j;
}
```

```click
verifying "repro.c";

predicate allpos(p: int32[], n: int32) {
    (0..n).all(|j| { p[j] > 0 })
}

int32 f(int32 p[2], int32 j) {
    views p[0..2];
    requires p[0] == 0;
    requires j == 2;
    ensures allpos(p, j);
} by {
    step_until(function.exit);
    unfold(allpos(p, j));
    close();
}
```

```expect
fail: could not establish `(0..(j as int32)).all
```
