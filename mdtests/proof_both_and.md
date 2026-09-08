# Exact conjunction subproofs

Both child proofs inherit the parent assumptions, but not each other's facts.
The nested universal goals retain their own binders.

```click
theorem reflexive_pair(x: int32) {
    ensures x == x and (x <= x and x >= x) by {
        both { normalize(); } and {
            both { normalize(); } and { normalize(); }
        }
    }
}

theorem quantified_pair() {
    ensures (forall (i: int32) { i == i }) and
            (forall (j: int32) { j <= j }) by {
        both { intro(); normalize(); } and { intro(); normalize(); }
    }
}
```

```expect
pass
```
