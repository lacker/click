# Integer let-satisfy does not fabricate a false existential claim

```click
theorem integer_exists_choose_false_claim() {
    requires exists (z: Integer) { z == z };
    ensures exists (k: Integer) { k != k } by {
        let (candidate: Integer) satisfy { candidate == candidate };
        witness(k = candidate);
        assumption();
    }
}
```

```expect
fail: assumption
```
