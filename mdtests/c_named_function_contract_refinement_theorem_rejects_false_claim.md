# A contract-refinement theorem rejects a false behavioral implication

The theorem is not a cast or an annotation: its leaf checker must establish
that the concrete postcondition entails the named contract's postcondition.

```c filename=refinement_theorem_false_claim.c
int32 return_zero() {
    return 0;
}
```

```click
verifying "refinement_theorem_false_claim.c";

contract int32 Positive() {
    ensures result > 0;
}

int32 return_zero() {
    ensures result == 0;
} by {
    execute();
    simp();
}

theorem zero_is_positive() {
    ensures Positive(&return_zero) by {
        unfold(Positive);
        simp();
    }
}
```

```expect
fail: contract-refinement proof does not establish `Positive(&return_zero)`
```
