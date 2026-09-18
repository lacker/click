# Equal endpoints give equal range folds

A range fold reads nothing but its endpoints, its initial value, and its body,
so two folds that agree on all four denote the same `Integer`.  The endpoints
need only be *equal*, not the same term: an available `a == b`, or the affine
normal form that makes `(hi - 1) + 1` and `hi` the same endpoint.  The second
form is the one an induction step needs, to carry the append law's `end + 1`
back to the goal's `hi`.

```click
theorem fold_endpoints_equal_from_an_equality(lo: int32, a: int32, b: int32) {
    requires a == b;
    ensures (lo..a).fold(0, |acc, k| { acc + to_integer(k) }) ==
        (lo..b).fold(0, |acc, k| { acc + to_integer(k) }) by {
        simp();
    }
}

theorem fold_endpoint_predecessor_successor(lo: int32, hi: int32) {
    ensures (lo..((hi - 1) + 1)).fold(0, |acc, k| { acc + to_integer(k) }) ==
        (lo..hi).fold(0, |acc, k| { acc + to_integer(k) }) by {
        simp();
    }
}
```

```expect
pass
```
