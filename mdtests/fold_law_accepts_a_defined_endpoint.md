# a fold law applies at an endpoint whose definedness is available

The range endpoint `hi - 1` is a partial machine subtraction, so capturing the
fold argument evaluates one path guarded by that subtraction being defined.
The `using` evidence states `0 < hi`, which decides the guard, so the capture
is accepted and the append law applies at the predecessor endpoint.

```click
theorem fold_appends_at_a_predecessor_endpoint(lo: int32, hi: int32) {
    requires 0 < hi;
    requires lo <= hi - 1;
    requires hi - 1 < 2147483647;
    ensures (lo..((hi - 1) + 1)).fold(0, |acc, k| { acc + to_integer(k) }) ==
        (lo..(hi - 1)).fold(0, |acc, k| { acc + to_integer(k) }) +
            to_integer(hi - 1) by {
        apply(integer_range_fold_append(
            (lo..(hi - 1)).fold(0, |acc, k| { acc + to_integer(k) })
        )) using {
            0 < hi;
            lo <= hi - 1;
            hi - 1 < 2147483647;
        }
    }
}
```

```expect
pass
```
