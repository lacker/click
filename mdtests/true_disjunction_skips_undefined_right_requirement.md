# A literal true disjunction does not require the unused native shift

A literally true left side leaves no case for the right side, so
`64u64 >= 64u64 or (1u64 << 64u64) == 2u64` lowers to its left side. A left
side that only the facts make true keeps the written disjunction: the proof
states it, and the right side's shift is owed only where the left fails.

```click
theorem guarded(s: uint64) {
    requires s >= 64u64 or (1u64 << s) == 2u64;
    ensures 1 == 1 by close();
}

theorem zero_instance() {
    ensures 1 == 1 by apply(guarded(64u64));
}

theorem known_zero_instance(s: uint64) {
    requires s >= 64u64;
    ensures 1 == 1 by {
        have s >= 64u64 or (1u64 << s) == 2u64 by {
            have s >= 64u64;
            close();
        }
        apply(guarded(s));
    }
}
```

```expect
pass
```
