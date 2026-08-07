# frontier-local statement facts

Facts about intermediate execution states are proved in the ordinary forward
proof, at the frontier where they hold. Static statement points can still name
the corresponding entry and exit snapshots.

```c filename=frontier_local_statement_facts.c
int32 frontier_local_statement_facts(int32 flag) {
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
verifying "frontier_local_statement_facts.c";

int32 frontier_local_statement_facts(int32 flag) {
    ensures result == 2
        and at(statement(1).exit, y) >= 0
        and at(statement(4).entry, y) >= 0
        and at(statement(4).exit, y) == 2
        and at(statement(5).entry, y) == 2 by {
        step();
        have flag == flag by {
            normalize();
        }
        reach(statement(1).exit)
        ensuring {
            fact y >= 0;
            fact y <= 1;
        }
        by {
            if flag != 0 {
                step();
                step();
            } else {
                step();
                step();
            }
        }
        have y >= 0 by {
            simp();
        }
        step();
        have y == 2 by {
            simp();
        }
        step();
        simp();
    }
}
```

```expect
pass
```
