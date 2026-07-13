# statement at snapshots

This checks `at(statement(N).entry, expr)` and
`at(statement(N).exit, expr)` after deterministic execution records statement
boundaries. Both `execute_rest()` and `execute_until(...)` use the same
one-statement snapshot behavior as repeated `execute_step()` calls.

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

```click
verifying "statement_at_snapshots.c";
verifying "statement_at_prefix_snapshots.c";

int32 set_first_to_seven(int32* p) {
    requires write(p[0..1]);

    ensures entry_is_old: at(statement(0).entry, p[0]) == old(p[0]) by {
        execute_rest();
        simp();
    }

    ensures exit_is_written: at(statement(0).exit, p[0]) == 7 by {
        execute_rest();
        simp();
    }

    ensures result_is_statement_exit: result == at(statement(0).exit, p[0]) by {
        execute_rest();
        simp();
    }
}

int32 set_first_twice(int32* p) {
    requires write(p[0..1]);

    ensures prefix_exit: at(statement(0).exit, p[0]) == 3 by {
        execute_until(statement(1));
        execute_rest();
        simp();
    }

    ensures adjacent_boundary:
        at(statement(0).exit, p[0]) == at(statement(1).entry, p[0]) by {
        execute_until(statement(1));
        execute_rest();
        simp();
    }

    ensures final_exit: at(statement(1).exit, p[0]) == 7 by {
        execute_until(statement(1));
        execute_rest();
        simp();
    }
}
```

```expect
pass
```
