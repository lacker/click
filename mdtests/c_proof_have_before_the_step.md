# the same `have`-before-the-step shape in a C proof

The companion of `mdtests/pure_have_sees_proved_facts.md`: the identical proof
shape stated inside a C function's proof, so the two paths are pinned together.
A pure theorem's in-proof lowering and a fixed-state proof's lowering consult
the same kind of fact set — the premises in scope plus the facts proved so far —
and neither is allowed to drift into consulting nothing.

`views p[lo..hi]` supplies the viewed range here in place of the pure
theorem's `viewable` premise; the three order `have`s that place `hi - 1`
inside it are the same, and so is the fourth `have` that writes the read down.

```c filename=c_proof_have_before_the_step.c
int32 last_of_view(int32 *p, int32 lo, int32 hi) {
    return hi;
}
```

```click
verifying "c_proof_have_before_the_step.c";

int32 last_of_view(int32 *p, int32 lo, int32 hi) {
    requires 0 <= lo;
    requires lo < hi;
    views p[lo..hi];
    ensures result == hi by {
        have 0 < hi by { arithmetic() using { 0 <= lo; lo < hi; } }
        have lo <= hi - 1 by { arithmetic() using { lo < hi; 0 < hi; } }
        have hi - 1 < hi by { arithmetic() using { 0 < hi; } }
        have to_integer(p[hi - 1]) == to_integer(p[hi - 1]) by { simp(); }
        step();
        simp();
    }
}
```

```expect
pass
```
