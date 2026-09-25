# A strict transitive bound also implies a weak bound

```click
theorem weak_transitive_bound(j: int32, hi: int32, n: int32) {
    requires j < hi;
    requires hi <= n;
    ensures j <= n by {
        arithmetic() using { j < hi; hi <= n; }
    }
}
```

```expect
pass
```
