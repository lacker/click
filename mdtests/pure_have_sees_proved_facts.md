# a `have` inside a pure theorem sees the theorem's premises and the facts proved so far

A term the verifier cannot see is defined on its own is repaired by proving the
missing fact first: state it with `have ... by { ... }` before the step that
needs it, and the step then goes through. No new syntax is involved, so the
same shape has to work in a pure theorem and in a C proof.

Here the array read `p[hi - 1]` has three evaluation conditions: `hi - 1` must
not overflow, its 4 bytes must be viewable, and the read must denote the value
the state holds. The theorem's `requires` alone do not decide the first two,
because `viewable(p[lo..hi])` covers one cell only where that cell's index
bounds inside the range are themselves established order facts. The three
`have`s establish exactly those bounds, and the fourth `have` — the one that
writes the read down — is discharged against them.

The fact set a pure in-proof lowering consults is the theorem's `requires` plus
the facts proved so far at that point, the same set a fixed-state proof's
lowering uses.

```click
theorem last_cell(p: int32[], lo: int32, hi: int32) {
    requires 0 <= lo;
    requires lo < hi;
    requires hi >= 0 and viewable(p[lo..hi]);
    ensures lo < hi by {
        have 0 < hi by { arithmetic() using { 0 <= lo; lo < hi; } }
        have lo <= hi - 1 by { arithmetic() using { lo < hi; 0 < hi; } }
        have hi - 1 < hi by { arithmetic() using { 0 < hi; } }
        have to_integer(p[hi - 1]) == to_integer(p[hi - 1]) by { simp(); }
        assumption();
    }
}
```

```expect
pass
```
