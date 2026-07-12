# statement at snapshots

This checks `at(statement(N).entry, expr)` and
`at(statement(N).exit, expr)` after `execute_step()` records the statement's
entry and exit states.

```c filename=statement_at_snapshots.c
int32 set_first_to_seven(int32* p) {
    p[0] = 7;
    return p[0];
}
```

```click
verifying "statement_at_snapshots.c";

int32 set_first_to_seven(int32* p) {
    requires write(p[0..1]);

    ensures entry_is_old: at(statement(0).entry, p[0]) == old(p[0]) by {
        execute_step();
        execute_rest();
        simp();
    }

    ensures exit_is_written: at(statement(0).exit, p[0]) == 7 by {
        execute_step();
        execute_rest();
        simp();
    }

    ensures result_is_statement_exit: result == at(statement(0).exit, p[0]) by {
        execute_step();
        execute_rest();
        simp();
    }
}
```

```expect
pass
```
