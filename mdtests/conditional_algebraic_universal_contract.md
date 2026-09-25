# A conditional universal survives post-return proof checking

The antecedent and consequent both contain freshly lowered binders. The
post-return `have` also exercises reported algebraic introduction metadata.

```c filename=conditional_algebraic_universal_contract.c
int32 report(int32 *v) { return 0; }
```

```click
verifying "conditional_algebraic_universal_contract.c";
spec enum Choice { First, Second }
function pick(v: int32[], choice: Choice) -> int32 {
    v[0]
}
int32 report(int32 *v) {
    ensures result == 0 implies
        (forall (k: int32) { v[k] == 0 }) implies
        forall (choice: Choice) { pick(v, choice) == 0 };
} by {
    have (forall (k: int32) { v[k] == 0 }) implies
        forall (choice: Choice) { pick(v, choice) == 0 } by {
        intro(); intro();
        instantiate(forall (k: int32) { v[k] == 0 }, 0) using {};
        unfold(pick(v, choice)); assumption();
    }
    step();
    have result == 0 implies
        (forall (k: int32) { v[k] == 0 }) implies
        forall (choice: Choice) { pick(v, choice) == 0 } by {
        intro(); assumption();
    }
    simp();
}
```

```expect
pass
```
