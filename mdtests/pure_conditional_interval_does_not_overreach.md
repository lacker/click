# the conditional's interval is the hull, not one arm

`if c { 1 } else { 0 } <= 0` holds on the else arm and fails on the then arm,
and nothing here decides `c`. The hull `0..1` leaves the comparison undecided,
so the claim is refused rather than read off the arm that happens to satisfy
it.

```click
theorem indicator_is_not_at_most_zero(x: int32) {
    ensures if x == 0 { 1 } else { 0 } <= 0 by {
        simp();
    }
}
```

```expect
fail: could not establish `(if x == 0 { 1 } else { 0 }) <= 0`
```
