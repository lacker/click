# Pure Integer existential elimination retains a checked symbolic witness

```click
theorem integer_exists_choose() {
    requires exists (z: Integer) { z == z };
    ensures exists (k: Integer) { k == k } by {
        choose(candidate from requirement 0);
        witness(k = candidate);
        assumption();
    }
}
```

```expect
pass
```
