# an unfolded quantifier does not capture a same-named argument

`allpos(p, 2)` requires `p[0] > 0`, and `p[0] == 0`. Unfolding the predicate
substitutes the C parameter `i` for `n` under a binder also written `i`; the
Surface renames the binder, and the kernel binds the quantifier by its
variable alone, so the argument keeps naming the C parameter. The body used to
lower to `forall i. 0 <= i and i < i implies ...`, which is vacuous, and the
false claim verified.

```c filename=repro.c
int32 f(int32 p[2], int32 i) {
    return i;
}
```

```click
verifying "repro.c";

predicate allpos(p: int32[], n: int32) {
    forall (i: int32) { 0 <= i and i < n implies p[i] > 0 }
}

int32 f(int32 p[2], int32 i) {
    views p[0..2];
    requires p[0] == 0;
    requires i == 2;
    ensures allpos(p, i);
} by {
    step_until(function.exit);
    unfold(allpos(p, i));
    close();
}
```

```expect
fail: could not establish `forall
```
