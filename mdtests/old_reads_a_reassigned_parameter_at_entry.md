# `old(n)` and every snapshot read a reassigned parameter's entry value

The body reassigns its parameter. In a contract, `old(n)` has always meant
the value `n` was passed. In a proof script it did not: `old` moved the memory
to the entry state but kept the proof's current binding for `n`, and so did a
proof mark taken before the parameter's first statement, since the entry
state does not yet bind the parameter as a local and the mark fell back to the
same current binding. After `n = n - 1`, `old(n) == 0` verified and
`old(n) == 1` was refused, the reverse of the reference. Both now read the
entry value, as the contract does and as `at(statement(0).entry, n)` already
did.

```c filename=old_reads_a_reassigned_parameter_at_entry.c
int32 dec(int32 n) {
    n = n - 1;
    return n;
}
```

```click
verifying "old_reads_a_reassigned_parameter_at_entry.c";

int32 dec(int32 n) {
    requires n == 1;
    ensures result == old(n) - 1;
} by {
    mark start;
    step();
    have n == 0 by { simp(); }
    have old(n) == 1 by { simp(); }
    have at(function.entry, n) == 1 by { simp(); }
    have at(start, n) == 1 by { simp(); }
    have at(statement(0).entry, n) == 1 by { simp(); }
    step();
    simp();
}
```

```expect
pass
```
