# A `rewrite` that finds nothing to replace shows both lowered terms

`rewrite(a == b)` replaces `a` by `b` in the current goal and is refused when
the goal contains no `a`. The refusal used to say only that the equality "does
not occur in the current goal", which is the right verdict and no help at
all when the author is sure `a` is in the goal: the usual cause is that the
equality's left side lowered to a different kernel term than the goal's, for
example a load of another width, or a value where the goal has a load. Gaps
67 and 70 in [`rbtree-example.md`](../issues/rbtree-example.md) were both a
4-byte read of an 8-byte cell hidden behind that sentence.

The refusal now prints the lowered equality and the lowered goal, in the
kernel's own spelling, so the mismatch is visible where it is decided. Here
the mismatch is honest: the goal `c == c` names no `a`.

```c filename=rw.c
int pick(int a, int b, int c) {
    return c;
}
```

```click
verifying "rw.c";

int pick(int a, int b, int c) {
    requires a == b;
    ensures result == c;
} by {
    have c == c by {
        rewrite(a == b);
        normalize();
    }
    execute();
    simp();
}
```

```expect
fail: `rewrite` equality does not occur in the current goal
  equality: v0 == v1 is true
  goal: v2 == v2 is true
```
