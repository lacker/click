# labeled statement execution

Statement labels are stable proof-facing names for execution targets and
snapshots. The numeric statement ID appears only where the label is declared.

```c filename=labeled_statement_execution.c
int32 labeled_statement_execution(int32 flag) {
    int32 y;
    if (flag) {
        y = 1;
    } else {
        y = 0;
    }
    y = 2;
    return y;
}
```

```click
verifying "labeled_statement_execution.c";

int32 labeled_statement_execution(int32 flag) {
    for statement(1) as choose {
        assert flag == flag by auto;
    }

    for statement(4) as update {
        assert y >= 0 by auto;
    }

    for statement(5) as done {
        assert y == 2 by auto;
    }

    ensures result == 2
        and at(choose.exit, y) >= 0
        and at(update.entry, y) >= 0
        and at(update.exit, y) == 2
        and at(done.entry, y) == 2 by {
        execute_step();
        advance(choose.exit)
        ensuring {
            fact y >= 0;
            fact y <= 1;
        }
        by {
            if flag != 0 {
                execute_then_step();
                execute_step();
            } else {
                execute_else_step();
                execute_step();
            }
        }
        execute_until(done);
        execute_step();
        simp();
    }
}
```

```expect
pass
```
