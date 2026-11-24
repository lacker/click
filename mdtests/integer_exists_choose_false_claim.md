# Integer let-satisfy does not fabricate a false existential claim

```click
theorem integer_exists_choose_false_claim() {
    requires exists (z: Integer) { z == z };
    ensures exists (k: Integer) { k != k } by {
        let candidate = obtain(exists (candidate: Integer) { candidate == candidate });
        witness(candidate);
        close();
    }
}
```

```expect
fail: could not establish `candidate != candidate`
```
