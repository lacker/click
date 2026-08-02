# Click array refs preserve memory snapshots

This checks that pure Click functions and predicates can receive arrays from
different memory states. In particular, `old(p)` as an array argument should
carry entry-state memory, not just the old pointer value.

```c filename=old_count_after_write.c
int32 old_count_after_write(int32 p[1], int32 x) {
    int32 before;
    before = p[0];
    p[0] = x;
    return before;
}
```

```c filename=keep_first_change_second.c
int32 keep_first_change_second(int32 p[2], int32 x) {
    p[1] = x;
    return 0;
}
```

```c filename=identity_two_arrays.c
int32 identity_two_arrays(int32 p[1], int32 q[1]) {
    return 0;
}
```

```click
verifying "old_count_after_write.c";
verifying "keep_first_change_second.c";
verifying "identity_two_arrays.c";

predicate same_first(int32 a[], int32 b[]) {
    a[0] == b[0]
}

int32 old_count_after_write(int32 p[1], int32 x) {
    requires loadable(p[0..1]);
    consumes p[0..1];
    ensures result_was_old_value: count(old(p), 0, 1, result) == 1 by auto;
}

int32 keep_first_change_second(int32 p[2], int32 x) {
    requires loadable(p[0..2]);
    consumes p[1..2];
    ensures first_cell_preserved: same_first(p, old(p)) by {
        execute();
        unfold(same_first);
        simp();
    }
}

int32 identity_two_arrays(int32 p[1], int32 q[1]) {
    requires loadable(p[0..1]);
    requires loadable(q[0..1]);
    requires same_first(p, q);
    ensures exact_opaque_fact: same_first(p, q) by auto;
    ensures unfolded_requirement: p[0] == q[0] by {
        execute();
        unfold(same_first);
        simp();
    }
}
```

```expect
pass
```
