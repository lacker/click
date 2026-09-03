# Grouped existential reasoning can use top-level choose and witness

Top-level existential operations in a grouped proof advance the checked
execution proof. `choose` refines an entry requirement before execution, and
`witness` refines an outcome claim after execution.

```c filename=grouped_witness.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "grouped_witness.c";

int32 identity(int32 x) {
    requires has_k: exists (k: int32) { k == x };
    ensures exists (j: int32) { j == x };
} by {
    choose(k from requirement has_k);
    execute();
    witness(j = k);
    simp();
}
```

```expect
pass
```
