# `solve` does not carry a predicate from one argument to another

`holds(b, p)` asks whether a boxed integer is `p`. Knowing that it is says
nothing about an unrelated `q`: with `b` the box of `0`, `holds(b, 0)` is `1`
and `holds(b, 1)` is `0`.

`close()` used to prove the theorem below. The certificate it found was made of
simple tactics: rewrite the goal's `1` to `holds(b, p)`, unfold both
applications, and rewrite by the premise. The last step was the unsound one. A
`rewrite` whose source is a composite term could not substitute through the
binder of an unfolded `match` arm, and instead of leaving the term alone it
replaced each `match` by a placeholder `0`, so the goal became `0 == 0`
([`rewrite_keeps_a_match_it_cannot_substitute_through.md`](rewrite_keeps_a_match_it_cannot_substitute_through.md)
is that step by itself).

The effect reached C contracts. A postcondition that named the wrong node, or
an empty list, as an argument of a list predicate was accepted on the strength
of the right one, which is how the unchanged Linux `rb_next` proof found it:
a contract claiming the predecessor verified.

```click quick-solve
spec enum Box { Box(int32) }

function holds(b: Box, p: int32) -> int32 {
    match b {
        Box::Box(q) => if q == p { 1 } else { 0 },
    }
}

theorem one_argument_says_nothing_about_another(b: Box, p: int32, q: int32) {
    requires holds(b, p) == 1;

    ensures holds(b, q) == 1 by {
        close();
    }
}
```

```expect
fail: could not establish `holds(b, q) == 1`
```
