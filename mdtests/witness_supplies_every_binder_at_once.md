# One `witness` supplies every binder of an existential

`witness { name: value, ... }` gives each binder of the existential goal its
value, in the order written, as one step. `obtain` is its dual: it opens an
available existential and binds every name at once.

```click
theorem split_sum(n: Integer) {
    requires 0 <= n;
    ensures exists (a: Integer, b: Integer) { a + b == n and 0 <= a and 0 <= b } by {
        witness { a: n, b: 0 };
        simp();
    }
}

theorem reopen(n: Integer) {
    requires exists (a: Integer, b: Integer) { a + b == n and 0 <= a and 0 <= b };
    ensures exists (b: Integer, a: Integer) { a + b == n and 0 <= a and 0 <= b } by {
        obtain (a: Integer, b: Integer) { a + b == n and 0 <= a and 0 <= b }
        witness { b: b, a: a };
        simp();
    }
}
```

```expect
pass
```
