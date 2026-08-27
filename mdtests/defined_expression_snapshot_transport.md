# Defined expressions survive unrelated stores

A recorded `defined(...)` premise keeps naming its certified entry fact after
an unrelated write changes the current memory snapshot. The second explicit
step must use that transported fact rather than re-evaluating the expression
against the later heap.

```c filename=defined_expression_snapshot_transport.c
struct pair {
    int32 value;
    int32 other;
};

int32 increment_after_other_write(struct pair* pair) {
    pair->other = 0;
    return pair->value + 1;
}
```

```click
verifying "defined_expression_snapshot_transport.c";

int32 increment_after_other_write(struct pair* pair) {
    requires defined(pair->value + 1);
    owns pair[0..2];

    ensures result == old(pair->value) + 1;
} by {
    step();
    step();
    have pair->value == old(pair->value) by {
        normalize();
    }
    simp();
}
```

```expect
pass
```
