# A current view does not cover an uncovered neighbor

The body read is outside the range supplied by the view and must be rejected
by static definition validation.

```click
resource viewed_neighbor(p: int32*) {
    views p[0..1];
    fact p[1] == 0;
}
```

```expect
fail: without a covering contained memory resource with current read authority
```
