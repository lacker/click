# a fact proved inside a closed `have` body does not reach a later pure step

The fact set a pure in-proof lowering consults is the premises in scope at that
point, so it must not contain a fact that is no longer in scope. A nested
`have` body is its own scope: what it proves justifies its own statement and
nothing else, and once it closes only that statement survives.

Here `lo <= hi - 1` is proved only inside the body of `have 0 <= hi`.
That private fact must not help establish the later explicit claim
`viewable(p[hi - 1..hi])`. Logical reads themselves need no such claim.

```click
theorem last_cell(p: int32[], lo: int32, hi: int32) {
    requires 0 <= lo;
    requires lo < hi;
    requires hi >= 0 and viewable(p[lo..hi]);
    ensures lo < hi by {
        have 0 < hi by { arithmetic() using { 0 <= lo; lo < hi; } }
        have hi - 1 < hi by { arithmetic() using { 0 < hi; } }
        have 0 <= hi by {
            have lo <= hi - 1 by { arithmetic() using { lo < hi; 0 < hi; } }
            arithmetic() using { 0 <= lo; 0 < hi; }
        }
        have viewable(p[hi - 1..hi]) by { simp(); }
        assumption();
    }
}
```

```expect
fail: narrowing that range needs `lo <= (hi - 1)`
```
