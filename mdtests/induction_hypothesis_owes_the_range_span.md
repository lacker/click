# An induction hypothesis owes a moved range's span

The hypothesis `let ih = induct(hi)` gives is the theorem's own statement at the
smaller argument, and that statement includes the span halves of every range
it names: the theorem's proof assumed them, so a use of the theorem, including
a use by its own induction, owes them.

Here the range moves with the induction variable: the hypothesis names
`v[lo..hi - 1]`, a range this proof narrowed to rather than one a clause
stated. The application asks the ordinary solver for the span facts
`0 <= hi - 1 - lo` and `hi - 1 - lo <= 1073741823`.

```click
theorem hypothesis_owes_the_range_span(v: int32[], lo: int32, hi: int32) {
    views v[lo..hi];
    requires 0 <= lo;
    requires 0 <= hi;
    requires hi <= 1073741823;
    ensures 0 <= hi by {
        let ih = induct(hi);
        if hi <= lo {
            close();
        } else {
            have lo < hi;
            have 0 <= to_integer(hi - 1) by { close() using { 0 <= lo; lo < hi; }; }
            have to_integer(hi - 1) < to_integer(hi) by { close() using { 0 <= lo; lo < hi; }; }
            have to_integer(lo) <= to_integer(hi - 1) by { close() using { 0 <= lo; lo < hi; }; }
            have to_integer(hi - 1) <= 1073741823 by {
                close() using { 0 <= hi; hi <= 1073741823; };
            }
            have viewable(v[lo..hi - 1]);
            apply(ih(hi - 1));
            close();
        }
    }
}
```

```expect
pass
```
