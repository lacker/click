# loop exit snapshots in execution proofs

This checks that modular execution across a verified loop records its unique
exit state. The proof derives the loop result from the invariant and the false
exit condition, then carries that fact through the return. Individual
`execute_step()` calls enter loop iterations; `execute_until(...)` deliberately
applies the verified abstract loop rule.

```c filename=loop_exit_snapshot.c
int32 count_from_to(int32 i, int32 n) {
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "loop_exit_snapshot.c";

int32 count_from_to(int32 i, int32 n) {
    requires 0 <= i and i <= n;
    requires n < 2147483647;

    for loop(0) as count {
        assert i <= n;
        invariant 0 <= i and i <= n;
    }

    ensures result == n and at(count.exit, i) == n by {
        execute_until(statement(2));
        have at(count.exit, i) == n by {
            simp();
        }
        execute_step();
        simp();
    }

    ensures batch_execution_records_exit: at(count.exit, i) == n by {
        execute_rest();
        simp();
    }

    ensures execute_until_crosses_loop: result == n by {
        execute_until(statement(2));
        have at(count.exit, i) == n by {
            simp();
        }
        execute_step();
        simp();
    }

    ensures advance_to_loop_exit: result == n by {
        advance(count.exit)
        ensuring {
            fact i == n;
        }
        by {
            execute_until(statement(2));
        }
        execute_step();
        simp();
    }
}
```

```expect
pass
```
