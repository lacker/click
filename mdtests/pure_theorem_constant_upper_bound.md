# pure theorem constant upper-bound weakening

The default pure-theorem prover must retain a checked surface certificate when
it derives a larger strict upper bound from a smaller strict upper bound.

```click
theorem small(x: int32) {
    requires x < 10;
    ensures x < 20;
}
```

```expect
pass
```
