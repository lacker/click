# Integer choose rejects a name already in scope

```click
theorem integer_exists_choose_scope(candidate: Integer) {
    requires exists (z: Integer) { z == z };
    ensures exists (k: Integer) { k == k } by {
        choose(candidate from requirement 0);
        witness(k = candidate);
        assumption();
    }
}
```

```expect
fail: already in scope
```
