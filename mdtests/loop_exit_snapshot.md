# loop exit snapshots in execution proofs

This checks that modular execution across a verified loop records its unique
exit state. The proof derives the loop result from the invariant and the false
exit condition, then carries that fact through the return. Individual
`step()` calls enter loop iterations; `execute_until(...)` deliberately
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
    ensures result == n and at(count.exit, i) == n;
    ensures batch_execution_records_exit: at(count.exit, i) == n;
    ensures execute_until_crosses_loop: result == n;
    ensures advance_to_loop_exit: result == n;
} by {
    loop as count {
        invariant 0 <= i and i <= n;
    }
    step();
    simp();
}
```

```expect
pass
```
