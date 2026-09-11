# Integer choose rejects an unavailable requirement

```click
theorem integer_exists_choose_missing_requirement() {
    requires exists (z: Integer) { z == z };
    ensures exists (k: Integer) { k == k } by {
        choose(candidate from requirement 1);
        witness(k = candidate);
        assumption();
    }
}
```

```expect
fail: out of range
```
