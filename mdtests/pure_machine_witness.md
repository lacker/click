# Pure witnesses instantiate machine values and pointers

```click
theorem split_sum(n: int32) {
    requires 0 <= n and n <= 100;
    ensures exists (a: int32, b: int32) { a + b == n and 0 <= a and 0 <= b } by {
        witness { a: n, b: 0 };
        simp();
    }
}

theorem pointer_identity(p: int32*) {
    ensures exists (q: int32*) { q == p } by {
        witness { q: p };
        simp();
    }
}
```

```expect
pass
```
