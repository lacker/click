# an unfolded quantifier with a same-named argument proves a true claim

The positive twin of
`mdtests/an_unfolded_quantifier_does_not_capture_a_same_named_argument.md`
and `mdtests/an_unfolded_range_all_does_not_capture_a_same_named_argument.md`:
the argument `m` is spelled like both binders, the claim is true, and the
proof goes through. The fix is a rename, not a refusal of the spelling.

```c filename=repro.c
int32 f(int32 p[2], int32 m) {
    return m;
}
```

```click
verifying "repro.c";

predicate allpos(p: int32[], n: int32) {
    forall (m: int32) { 0 <= m and m < n implies p[m] > 0 }
}

predicate allpos_range(p: int32[], n: int32) {
    (0..n).all(|m| { p[m] > 0 })
}

int32 f(int32 p[2], int32 m) {
    views p[0..2];
    requires p[0] > 0;
    requires p[1] > 0;
    requires m == 2;
    ensures allpos(p, m) by { step_until(function.exit); unfold(allpos(p, m)); close(); }
    ensures allpos_range(p, m) by { step_until(function.exit); unfold(allpos_range(p, m)); close(); }
}
```

```expect
pass
```
