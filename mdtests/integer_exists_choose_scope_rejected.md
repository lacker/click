# Integer let-satisfy rejects a name already in scope

```click
theorem integer_exists_choose_scope(candidate: Integer) {
    requires exists (z: Integer) { z == z };
    ensures exists (k: Integer) { k == k } by {
        let candidate = obtain(exists (candidate: Integer) { candidate == candidate });
        witness(candidate);
        close();
    }
}
```

```expect
fail: already in scope
```
