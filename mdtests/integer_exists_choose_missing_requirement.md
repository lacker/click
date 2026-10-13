# Existential elimination rejects an unavailable fact

```click
theorem integer_exists_choose_missing_requirement() {
    requires exists (z: Integer) { z == z };
    ensures exists (k: Integer) { k == k } by {
        obtain (candidate: Integer) { candidate != candidate }
        witness { k: candidate };
        assumption();
    }
}
```

```expect
fail: required existential fact is not available
```
