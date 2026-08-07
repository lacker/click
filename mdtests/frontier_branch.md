# frontier-local branch proofs

The `branch` tactic consumes the C `if` at the current execution frontier.
Nested branches follow the source nesting, including a tail-nested branch whose
join is also the containing branch's join.

```c filename=nested_branch.c
int32 nested_branch(int32 x, int32 y) {
    int32 result;
    if (x > 0) {
        if (y > 0) {
            result = 1;
        } else {
            result = 2;
        }
    } else {
        result = 3;
    }
    return result;
}
```

```click
verifying "nested_branch.c";

int32 nested_branch(int32 x, int32 y) {
    ensures result > 0 by {
        step();
        branch {
            ensuring {
                fact at(statement(6).entry, c(result)) > 0;
            }
            then {
                branch {
                    ensuring {
                        fact at(statement(6).entry, c(result)) > 0;
                    }
                    then {
                        step();
                    }
                    else {
                        step();
                    }
                }
            }
            else {
                step();
            }
        }
        step();
        simp();
    }
}
```

```expect
pass
```
