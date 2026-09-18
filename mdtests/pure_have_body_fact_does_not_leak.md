# a fact proved inside a closed `have` body does not reach a later pure step

The fact set a pure in-proof lowering consults is the premises in scope at that
point, so it must not contain a fact that is no longer in scope. A nested
`have` body is its own scope: what it proves justifies its own statement and
nothing else, and once it closes only that statement survives.

Here `lo <= hi - 1` — one of the two order facts the read `p[hi - 1]` needs —
is proved only inside the body of `have 0 <= hi`. The body's own statement
`0 <= hi` does reach the later step, and is listed among the premises
consulted; `lo <= hi - 1` is not, and the read is refused exactly as it is when
nobody proved that fact at all. Add the same `have` at the outer level, as
`mdtests/pure_have_sees_proved_facts.md` does, and the read goes through.

```click
theorem last_cell(p: int32[], lo: int32, hi: int32) {
    requires 0 <= lo;
    requires lo < hi;
    requires hi >= 0 and loadable(p[lo..hi]);
    ensures lo < hi by {
        have 0 < hi by { arithmetic() using { 0 <= lo; lo < hi; } }
        have hi - 1 < hi by { arithmetic() using { 0 < hi; } }
        have 0 <= hi by {
            have lo <= hi - 1 by { arithmetic() using { lo < hi; 0 < hi; } }
            arithmetic() using { 0 <= lo; 0 < hi; }
        }
        have to_integer(p[hi - 1]) == to_integer(p[hi - 1]) by { simp(); }
        assumption();
    }
}
```

```expect
fail: not established: the 4 bytes at `p[hi - 1]` must be loadable
  established: `hi - 1` must not overflow; the read at `p[hi - 1]` must denote the value this state holds
  premises consulted (7, a premise that is a conjunction counted as its conjuncts): `0 < hi`, `lo < hi`, `(hi - 1) < hi`, `0 <= lo`, `0 <= hi`, `hi >= 0`, `loadable(p[lo..hi])`
```
