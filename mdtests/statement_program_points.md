# statement at states

This checks `at(region(N).entry, expr)` and
`at(region(N).exit, expr)` after deterministic execution records statement
boundaries. Both the implicit tail and `step_until(...)` use the same
one-statement state behavior as repeated `step()` calls.

```c filename=statement_at_states.c
int32 set_first_to_seven(int32* p) {
    p[0] = 7;
    return p[0];
}
```

```c filename=statement_at_prefix_states.c
int32 set_first_twice(int32* p) {
    p[0] = 3;
    p[0] = 7;
    return p[0];
}
```

```c filename=statement_at_local_states.c
int32 state_local(int32 x) {
    int32 y;
    y = x;
    x = 7;
    return y;
}
```

```c filename=statement_at_local_array_states.c
int32 state_local_array() {
    int32 values[1];
    values[0] = 3;
    values[0] = 7;
    return values[0];
}
```

```click
verifying "statement_at_states.c";
verifying "statement_at_prefix_states.c";
verifying "statement_at_local_states.c";
verifying "statement_at_local_array_states.c";

int32 set_first_to_seven(int32* p) {
    consumes p[0..1];

    ensures entry_is_old: at(region(0).entry, p[0]) == old(p[0]);

    ensures exit_is_written: at(region(0).exit, p[0]) == 7;

    ensures result_is_statement_exit: result == at(region(0).exit, p[0]);
}

int32 set_first_twice(int32* p) {
    consumes p[0..1];

    ensures prefix_exit: at(region(0).exit, p[0]) == 3 by {
        step_until(region(1));
    }

    ensures adjacent_boundary:
        at(region(0).exit, p[0]) == at(region(1).entry, p[0]) by {
        step_until(region(1));
    }

    ensures final_exit: at(region(1).exit, p[0]) == 7 by {
        step_until(region(1));
    }
}


int32 state_local(int32 x) {
    ensures local_after_assignment:
        at(region(1).exit, y) == old(x);

    ensures parameter_before_assignment:
        at(region(2).entry, x) == old(x);

    ensures parameter_after_assignment:
        at(region(2).exit, x) == 7;

    ensures result_is_local_at_return:
        result == at(region(3).entry, y);
}


int32 state_local_array() {
    ensures first_store:
        at(region(1).exit, values[0]) == 3;

    ensures second_store:
        at(region(2).exit, values[0]) == 7;
}
```

```expect
pass
```
