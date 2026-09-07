# A contract-refinement theorem opens the contract explicitly

Contract parameters and the local refinement obligation become available only
after the proof explicitly unfolds the contract named in its conclusion.

```c filename=refinement_theorem_requires_unfold.c
int32 increment(int32 value) {
    return value + 1;
}
```

```click
verifying "refinement_theorem_requires_unfold.c";

contract int32 Increment(int32 input) {
    requires input < 2147483647;
    ensures result == input + 1;
}

int32 increment(int32 value) {
    requires value < 2147483647;
    ensures result == value + 1;
} by {
    execute();
    simp();
}

theorem increment_implements_increment() {
    ensures Increment(&increment) by {
        simp();
    }
}
```

```expect
fail: contract-refinement proof must begin with `unfold(Increment);`
```
