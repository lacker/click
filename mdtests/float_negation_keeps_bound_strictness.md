# Negation preserves equality at the endpoint of a closed float bound

```click quick-solve
theorem closed_bound(x: float) {
    requires x <= float32_from_bits(0x3f800000);
    ensures -x > float32_from_bits(0xbf800000) by {
        close();
    }
}
```

```expect
fail: could not establish
```
