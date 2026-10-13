# A loop body cites the iteration's entry value a refusal named

`mdtests/a_loop_body_goal_names_the_iteration_entry_value.md` is refused with
`goal: at(statement(3).entry, i) + 1 <= n`. The value it names is one a proof
can cite: the guard `i < n` held of it at the loop head, and citing that guard
in the printed spelling closes the goal.

```c filename=a_loop_body_cites_the_iteration_entry_value_a_refusal_named.c
int32 walk(int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "a_loop_body_cites_the_iteration_entry_value_a_refusal_named.c";

int32 walk(int32 n) {
    requires 0 <= n;
    ensures result == n;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
        initialize by { simp(); }
        preserve by {
            step();
            have i <= n by { arithmetic() using { at(statement(3).entry, i) < n; } }
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
