# A derivable ensure premise is not discharged by the call itself

Same callee and caller as
[`verified_call_ensure_premise_stays_implied`](verified_call_ensure_premise_stays_implied.md),
with the two discharging steps removed. The caller's `1 <= count` implies the
callee's `count > 0` premise but is not that premise, so the call publishes
the written implication and nothing else. Smart search finds no proof of the
consequent, because applying an ambient implication is an explicit step.

```c filename=ensure_premise_undischarged.c
int32 set_when_positive(int32 flag, int32* cell) {
    if (flag > 0) {
        cell[0] = 1;
    }
    return 0;
}

int32 undischarged_caller(int32 count, int32* cell) {
    int32 status = set_when_positive(count, cell);
    return status;
}
```

```click
verifying "ensure_premise_undischarged.c";

int32 set_when_positive(int32 flag, int32* cell) {
    owns cell[0..1];
    ensures flag > 0 implies cell[0] == 1;
} by {
    if flag > 0 {
        execute();
        simp();
    } else {
        execute();
        simp();
    }
}

int32 undischarged_caller(int32 count, int32* cell) {
    requires 1 <= count;
    owns cell[0..1];
    ensures cell[0] == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: unclosed goal: cell[0] == 1
```
