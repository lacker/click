# a fold law is refused when the endpoint is not known to be defined

This is the same append-law application with `0 < hi` removed from the `using`
evidence. Nothing there decides that `hi - 1` is defined, so the capture is
refused. The refusal names the offending subterm and the condition that is
missing, rather than blaming the initializer.

```click
theorem fold_rejects_an_undefined_endpoint(lo: int32, hi: int32) {
    requires lo <= hi - 1;
    requires hi - 1 < 2147483647;
    ensures (lo..((hi - 1) + 1)).fold(0, |acc, k| { acc + to_integer(k) }) ==
        (lo..(hi - 1)).fold(0, |acc, k| { acc + to_integer(k) }) +
            to_integer(hi - 1) by {
        apply(integer_range_fold_append(
            (lo..(hi - 1)).fold(0, |acc, k| { acc + to_integer(k) })
        )) using {
            lo <= hi - 1;
            hi - 1 < 2147483647;
        }
    }
}
```

```expect
fail: the fold's range endpoint denotes this value only where `int32 overflow(v1 - 1) is false` holds, and that is not available here
```
