# A pure machine witness must still prove its body

```click
theorem wrong_sum(n: int32) {
    requires 0 <= n and n <= 100;
    ensures exists (a: int32, b: int32) { a + b == n } by {
        witness { a: n, b: 1 };
        normalize();
    }
}
```

```expect
fail: did not normalize to true
```
