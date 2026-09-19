# `have viewable(...)` proves one cell of a viewable range in a C proof

The C companion of `mdtests/have_viewable_prefix_of_a_range.md`. The goal here
is the single cell the function is about to read, written as the one-element
range `p[hi - 1..hi - 1 + 1]`, and it is proved from the range the contract
gives plus the two order facts that place that cell inside it, and the bound
that makes that range a valid 32-bit byte extent.

This is the shape the kernel has always been willing to find on its own while
lowering a read of `p[hi - 1]`. Writing it down as a goal now goes through the
same decision, so a proof may state the fact before the step that needs it
instead of depending on the read's lowering to rediscover it.

```c filename=have_loadable_single_cell.c
int32 last_of_range(int32 *p, int32 lo, int32 hi) {
    return hi;
}
```

```click
verifying "have_loadable_single_cell.c";

int32 last_of_range(int32 *p, int32 lo, int32 hi) {
    requires 0 <= lo;
    requires lo < hi;
    requires hi - lo <= 1073741823;
    requires hi >= 0 and viewable(p[lo..hi]);
    ensures result == hi by {
        have 0 < hi by { arithmetic() using { 0 <= lo; lo < hi; } }
        have lo <= hi - 1 by { arithmetic() using { lo < hi; 0 < hi; } }
        have hi - 1 < hi by { arithmetic() using { 0 < hi; } }
        have 0 <= hi - lo by { arithmetic() using { 0 <= lo; lo < hi; } }
        have viewable(p[hi - 1..hi - 1 + 1]) by { simp(); }
        step();
        simp();
    }
}
```

```expect
pass
```
