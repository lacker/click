# Existential elimination rejects an unavailable fact

```click
theorem integer_exists_choose_missing_requirement() {
    requires exists (z: Integer) { z == z };
    ensures exists (k: Integer) { k == k } by {
        let candidate = obtain(exists (candidate: Integer) { candidate != candidate });
        witness(candidate);
        close();
    }
}
```

```expect
fail: required existential fact is not available
```
