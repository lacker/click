# Equal endpoints alone do not equate two range folds

Endpoint congruence is a congruence: it carries an endpoint equality into a
fold whose initial value and body are otherwise the same term.  Here the
endpoints are equal and the bodies are not, so the two folds must stay
unrelated.

```click
theorem fold_endpoints_reject_a_different_body(lo: int32, a: int32, b: int32) {
    requires a == b;
    ensures (lo..a).fold(0, |acc, k| { acc + to_integer(k) }) ==
        (lo..b).fold(0, |acc, k| { acc + to_integer(k) + 1 }) by {
        simp();
    }
}
```

```expect
fail: `simp` failed for `fold_endpoints_reject_a_different_body.ensures_0`: simplified proposition was not true: Integer equality is true
```
