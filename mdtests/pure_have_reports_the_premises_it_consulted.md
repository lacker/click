# a refused `have` in a pure theorem names the premises it actually consulted

The negative of `mdtests/pure_have_sees_proved_facts.md`: the three order
`have`s that place `hi - 1` inside the viewable range are missing, so the read
`p[hi - 1]` is still refused. What the refusal must show is the fact set the
lowering was given — here the theorem's four `requires` conjuncts — and which
condition they leave unestablished.

A refusal that reported `premises consulted: none` would be reporting a
verifier defect rather than a proof gap: it would mean the theorem's own
premises never reached the lowering, and then no amount of `have` could repair
the proof. This test pins that the premises reach it.

```click
theorem last_cell(p: int32[], lo: int32, hi: int32) {
    requires 0 <= lo;
    requires lo < hi;
    requires hi >= 0 and viewable(p[lo..hi]);
    ensures lo < hi by {
        have to_integer(p[hi - 1]) == to_integer(p[hi - 1]) by { simp(); }
        assumption();
    }
}
```

```expect
fail: not established: the 4 bytes at `p[hi - 1]` must be viewable
  established: `hi - 1` must not overflow; the read at `p[hi - 1]` must denote the value this state holds
  premises consulted (6, a premise that is a conjunction counted as its conjuncts): `lo < hi`, `0 <= lo`, `0 <= (hi - lo)`, `(hi - lo) <= 1073741823`, `hi >= 0`, `viewable(p[lo..hi])`
```
