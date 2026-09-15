# A quantified resource fact cannot read past its contained range

Quantified antecedent bounds are available when validating each guarded read,
but they do not enlarge the resource's authority. This fact includes `p[n]`
while the owned half-open range stops before it.

```click
resource too_wide(p: int32*, n: int32) {
    owns p[0..n];
    fact n >= 0;
    fact forall (k: int32) {
        0 <= k and k < n + 1 implies p[k] == 0
    };
}
```

```expect
fail: resource `too_wide` fact reads `p[k]` without a covering contained memory resource with current read authority
```
