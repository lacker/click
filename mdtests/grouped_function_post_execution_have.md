# Grouped proof facts after execution

`have` can establish a pure fact after execution reaches function exit. Its
scoped pure proof may choose an existential assumption and provide existential
witnesses without applying those goal-specific steps to the other contract
claims.

```c filename=grouped_post_have.c
int32 identity(int32 x) {
    return x;
}
```

```c filename=grouped_post_have_branch.c
int32 branch_value(int32 flag) {
    if (flag) {
        return 1;
    } else {
        return 0;
    }
}
```

```c filename=grouped_current_have.c
int32 current_have(int32 x) {
    return x;
}
```

```click
verifying "grouped_post_have.c";
verifying "grouped_post_have_branch.c";
verifying "grouped_current_have.c";

int32 identity(int32 x) {
    requires has_k: exists (int32 k) { k == x };
    immutable;
    ensures result == x;
    ensures result_witness: exists (int32 j) { j == result };
    ensures chosen_witness: exists (int32 j) { j == x };
} by {
    execute();
    have exists (int32 j) { j == result } by {
        witness(j = result);
        simp();
    }
    have exists (int32 j) { j == x } by {
        choose(k from requirement has_k);
        witness(j = k);
        simp();
    }
    frame();
    simp();
}

int32 branch_value(int32 flag) {
    ensures result >= 0;
} by {
    execute();
    have result >= 0 by simp;
    simp();
}

int32 current_have(int32 x) {
    ensures exists (int32 j) { j == result };
} by {
    have exists (int32 j) { j == x } by {
        witness(j = x);
        simp();
    }
    execute();
    simp();
}
```

```expect
pass
```
