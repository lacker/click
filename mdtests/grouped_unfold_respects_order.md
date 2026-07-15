# A later predicate unfold does not affect an earlier simp

Predicate unfolding and claim closing follow source order in a grouped proof.

```c filename=grouped_unfold_order.c
int32 identity(int32 x) {
    return x;
}
```

```click
predicate nonnegative(int32 x) {
    x >= 0
}

verifying "grouped_unfold_order.c";

int32 identity(int32 x) {
    requires nonnegative(x);
    ensures result >= 0;
} by {
    execute_rest();
    simp();
    unfold(nonnegative);
}
```

```expect
fail: left `identity.ensures_0` unproved
```
