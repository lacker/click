# A pure witness names the binder and both types on a mismatch

```click
theorem wrong_type(p: int64*) {
    ensures exists (q: int32*) { q == q } by {
        witness { q: p };
        simp();
    }
}
```

```expect
fail: witness `q` has the wrong type: expected int32*, got int64*
```
