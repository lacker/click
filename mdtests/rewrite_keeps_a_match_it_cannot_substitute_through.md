# `rewrite` does not replace an unfolded `match` it could not substitute through

`holds(b, p)` asks whether a boxed integer is `p`. The theorem below assumes it
is, and then "proves" it is not: it unfolds the application in the goal, so the
goal is a `match` on `b` whose arm binds the boxed value, and rewrites by the
premise `holds(b, p) == 1`. With `holds(b, p) == 0` and `holds(b, p) != 0` both
in hand, `contradiction` closes `0 == 1`.

The premise is satisfiable, so this must not verify. It used to, with simple
tactics only.

The rewrite's source, `holds(b, p)`, is a composite term rather than a
variable, and the walker that substitutes one term for another refuses to carry
a composite source under a binder of a `match` arm: it cannot tell whether the
arm's bound variable shadows something the source mentions. It reports that by
setting a flag and handing back a placeholder, the constant `0`. `rewrite`
kept the placeholder and dropped the flag, so the whole `match` term became
`0`, the goal became `0 == 0`, and `normalize()` closed it. Any `int32` claim
about an unfolded `match` could be closed that way, and `close()` found such
proofs on its own: a postcondition naming the wrong node verified.

A refused scope now leaves that term exactly as it was. Substituting by an
equality may always decline an occurrence, so the unrewritten term is a sound
result; here it means the rewrite finds no occurrence at all and says so.

```click
spec enum Box { Box(int32) }

function holds(b: Box, p: int32) -> int32 {
    match b {
        Box::Box(q) => if q == p { 1 } else { 0 },
    }
}

theorem a_true_premise_is_not_refuted(b: Box, p: int32) {
    requires holds(b, p) == 1;

    ensures 0 == 1 by {
        have holds(b, p) == 0 by {
            unfold(holds(b, p));
            rewrite(holds(b, p), 1);
            normalize();
        }
        have holds(b, p) != 0 by {
            rewrite(holds(b, p), 1);
            normalize();
        }
        contradiction(holds(b, p) == 0);
    }
}
```

```expect
fail: `rewrite` equality does not occur in the current goal
```
