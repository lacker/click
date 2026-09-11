# Integer choose freshens against an introduced ambient binder

```click
theorem integer_exists_choose_after_intro() {
    requires exists (z: Integer) { z == z };
    ensures forall (q: Integer) { exists (k: Integer) { k == k } } by {
        intro();
        choose(candidate from requirement 0);
        witness(k = candidate);
        assumption();
    }
}
```

```expect
pass
```
