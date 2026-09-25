# A guarded quantified postcondition expands and re-verifies

`vacuous` returns `0`, so its postcondition `result == 1 implies forall (k:
int32) { ... }` holds vacuously. `execute(); simp();` proves it, and claim
expansion renders the closer as a `have` of the claim followed by
`assumption()`. The `have` and the claim lower the same guarded quantifier
with independent fresh binders, and `assumption` used to compare an
implication only exactly, so the rewrite failed with "`assumption` did not
match any current proposition goal" although verification accepted the
original proof. The quantified alpha index now covers an implication chain
whose conclusion is quantified. `by_hand` states that `have` and
`assumption()` directly, as a user would.

The expansion regression in `src/surface/tests/expansion_tests.rs` expands
`vacuous` and re-verifies the rewrite.

```c filename=guarded_quantified_postcondition.c
int vacuous(int32* occ, int32 cap) {
    return 0;
}

int by_hand(int32* occ, int32 cap) {
    return 0;
}
```

```click
verifying "guarded_quantified_postcondition.c";

int vacuous(int32* occ, int32 cap) {
    owns occ[0..cap];
    requires 0 <= cap;
    ensures result == 1 implies forall (k: int32) {
        0 <= k and k < cap implies occ[k] == 1
    };
} by {
    execute();
    simp();
}

int by_hand(int32* occ, int32 cap) {
    owns occ[0..cap];
    requires 0 <= cap;
    ensures result == 1 implies forall (k: int32) {
        0 <= k and k < cap implies occ[k] == 1
    };
} by {
    execute();
    have result == 1 implies forall (k: int32) {
        0 <= k and k < cap implies occ[k] == 1
    } by {
        simp();
    }
    assumption();
    assumption();
}
```

```expect
pass
```
