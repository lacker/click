# statement at snapshots

This checks `at(statement(N).entry, expr)` and
`at(statement(N).exit, expr)` after deterministic execution records statement
boundaries. Both `execute()` and `execute_until(...)` use the same
one-statement snapshot behavior as repeated `step()` calls.

```c filename=statement_at_snapshots.c
int32 set_first_to_seven(int32* p) {
    p[0] = 7;
    return p[0];
}
```

```c filename=statement_at_prefix_snapshots.c
int32 set_first_twice(int32* p) {
    p[0] = 3;
    p[0] = 7;
    return p[0];
}
```

```c filename=statement_at_local_snapshots.c
int32 snapshot_local(int32 x) {
    int32 y;
    y = x;
    x = 7;
    return y;
}
```

```c filename=statement_at_local_array_snapshots.c
int32 snapshot_local_array() {
    int32 values[1];
    values[0] = 3;
    values[0] = 7;
    return values[0];
}
```

```click
verifying "statement_at_snapshots.c";
verifying "statement_at_prefix_snapshots.c";
verifying "statement_at_local_snapshots.c";
verifying "statement_at_local_array_snapshots.c";

int32 set_first_to_seven(int32* p) {
    consumes p[0..1];

    ensures entry_is_old: at(statement(0).entry, p[0]) == old(p[0]) by {
        execute();
        simp();
    }

    ensures exit_is_written: at(statement(0).exit, p[0]) == 7 by {
        execute();
        simp();
    }

    ensures result_is_statement_exit: result == at(statement(0).exit, p[0]) by {
        execute();
        simp();
    }
}

int32 set_first_twice(int32* p) {
    consumes p[0..1];

    ensures prefix_exit: at(statement(0).exit, p[0]) == 3 by {
        execute_until(statement(1));
        execute();
        simp();
    }

    ensures adjacent_boundary:
        at(statement(0).exit, p[0]) == at(statement(1).entry, p[0]) by {
        execute_until(statement(1));
        execute();
        simp();
    }

    ensures final_exit: at(statement(1).exit, p[0]) == 7 by {
        execute_until(statement(1));
        execute();
        simp();
    }
}


int32 snapshot_local(int32 x) {
    ensures local_after_assignment:
        at(statement(1).exit, y) == old(x) by {
        execute();
        simp();
    }

    ensures parameter_before_assignment:
        at(statement(2).entry, x) == old(x) by {
        execute();
        simp();
    }

    ensures parameter_after_assignment:
        at(statement(2).exit, x) == 7 by {
        execute();
        simp();
    }

    ensures result_is_local_at_return:
        result == at(statement(3).entry, y) by {
        execute();
        simp();
    }
}


int32 snapshot_local_array() {
    ensures first_store:
        at(statement(1).exit, values[0]) == 3 by {
        execute();
        simp();
    }

    ensures second_store:
        at(statement(2).exit, values[0]) == 7 by {
        execute();
        simp();
    }
}
```

```expect
pass
```
