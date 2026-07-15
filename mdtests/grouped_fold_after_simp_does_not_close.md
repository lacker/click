# A later fold does not affect an earlier simp

Resource folding and claim closing follow source order in a grouped proof.

```c filename=grouped_fold_order.c
int32 initialize(int32 p[]) {
    p[0] = 1;
    return 1;
}
```

```click
resource initialized(p: int32*) {
    owns p[0..1];
    fact p[0] == 1;
}

verifying "grouped_fold_order.c";

int32 initialize(int32 p[]) {
    consumes p[0..1];
    produces initialized(p);
} by {
    execute_rest();
    simp();
    fold(initialized(p));
}
```

```expect
fail: left `initialize.ensures_0` unproved
```
