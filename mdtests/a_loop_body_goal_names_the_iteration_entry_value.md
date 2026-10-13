# A loop body goal names the iteration's entry value

After `i = i + 1` no local holds the value `i` had when the iteration began.
That value is the loop head's, and a proof spells it
`at(statement(3).entry, i)`, so a refusal inside the body names it that way
too, rather than as a report-local `<unnamed A>`. Here the `have` cites
nothing, so the bound it claims stays open, and the goal reads in the
spelling the next attempt can cite:
`mdtests/a_loop_body_cites_the_iteration_entry_value_a_refusal_named.md`
closes the same goal by citing it.

```c filename=a_loop_body_goal_names_the_iteration_entry_value.c
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
verifying "a_loop_body_goal_names_the_iteration_entry_value.c";

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
            have i <= n by { arithmetic() using { } }
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
fail: goal: at(statement(3).entry, i) + 1 <= n
```
