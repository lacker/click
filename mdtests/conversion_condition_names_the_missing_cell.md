# an unestablished conversion condition names the cell, the premises, and the fix

`to_integer(p[hi - 1])` denotes a value only where the cell it reads is
viewable. A `requires` that states the whole range `p[lo..hi]` does not
establish that cell: the check wants the cell's index bounds inside the range as
established order facts, and it does not rearrange `lo < hi` into them.

The refusal has to say all of that in the reader's own names. It names the
subterm `p[hi - 1]`, the condition as a requirement on four bytes at that cell,
which of the evaluation's conditions did hold, the premises it consulted, why
the range premise was not enough, and the one-element range that repairs it.

```click
theorem cell_from_range(p: int32[], lo: int32, hi: int32) {
    requires 0 <= lo;
    requires lo < hi;
    requires hi >= 0 and viewable(p[lo..hi]);
    ensures to_integer(p[hi - 1]) == to_integer(p[hi - 1]) by { simp(); }
}
```

```expect
fail: its subterm `p[hi - 1]` denotes a value only where 3 conditions of that evaluation hold, and the premises in scope where it is stated establish 2 of them, not this one.
  not established: the 4 bytes at `p[hi - 1]` must be viewable
  established: `hi - 1` must not overflow; the read at `p[hi - 1]` must denote the value this state holds
  premises consulted (6, a premise that is a conjunction counted as its conjuncts): `lo < hi`, `0 <= lo`, `0 <= (hi - lo)`, `(hi - lo) <= 1073741823`, `hi >= 0`, `viewable(p[lo..hi])`
  why that was not enough: `viewable(p[lo..hi])` is a premise here and was consulted.
```
