# Integer choose does not fabricate a false existential claim

```click
theorem integer_exists_choose_false_claim() {
    requires exists (z: Integer) { z == z };
    ensures exists (k: Integer) { k != k } by {
        choose(candidate from requirement 0);
        witness(k = candidate);
        assumption();
    }
}
```

```expect
fail: assumption
```
