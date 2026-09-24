# Grouped existential reasoning can use top-level let-satisfy and witness

Top-level existential operations in a grouped proof advance the checked
execution proof. `let (...) satisfy` opens an entry fact before execution, and
`witness` refines an outcome claim after execution.

```c filename=grouped_witness.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "grouped_witness.c";

int32 identity(int32 x) {
    requires exists (k: int32) { k == x };
    ensures exists (j: int32) { j == x };
} by {
    let (k: int32) satisfy { k == x };
    execute();
    witness(j = k);
    simp();
}
```

```expect
pass
```
