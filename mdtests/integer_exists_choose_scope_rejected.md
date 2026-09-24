# Integer let-satisfy rejects a name already in scope

```click
theorem integer_exists_choose_scope(candidate: Integer) {
    requires exists (z: Integer) { z == z };
    ensures exists (k: Integer) { k == k } by {
        let (candidate: Integer) satisfy { candidate == candidate };
        witness(k = candidate);
        assumption();
    }
}
```

```expect
fail: already in scope
```
