# A false bare `transport` after execution is refused as at a frontier

A bare `transport(source, target)` at function exit, after
`step_until(function.exit)`, is planned exactly as it is between execution steps: its source alone is tried as the premise, then the
premise planner selects frame evidence. When nothing carries a false target,
the refusal is the source-only one, which names the store to `a[i]` between
the two states, the same refusal
`a_false_transport_in_a_branch_arm_is_refused_as_on_the_main_line.md` expects
before execution.

```c filename=a_false_bare_transport_after_execution_is_refused_as_at_a_frontier.c
void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    a[i] = 1;
}
```

```click
verifying "a_false_bare_transport_after_execution_is_refused_as_at_a_frontier.c";

void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    requires 0 <= i;
    requires i < n;
    requires 0 <= m;
    requires m < n;
    requires m != i;
    requires n <= 1073741823;
    owns a[0..n];
    ensures a[m] == old(a[m]);
} by {
    mark entry;
    step();
    step_until(function.exit);
    transport(at(entry, a[m]) == at(entry, a[m]), at(entry, a[m]) == 5);
    close();
}
```

```expect
fail: `transport` found no frame evidence carrying its source fact to the target's state
```
