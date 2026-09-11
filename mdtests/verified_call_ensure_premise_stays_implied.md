# A derivable ensure premise stays an implication for the proof to discharge

The callee guarantees the written cell only while its flag is positive. The
caller knows `1 <= count`, which implies the premise but is not that premise,
so the call publishes the ensure as the implication it was written as. The
proof spells the two steps the kernel no longer takes for it: an arithmetic
`have` that makes the premise exactly available, then `extract`, whose
bounded modus ponens over that implication adds the consequent.

```c filename=ensure_premise_flag.c
int32 set_when_positive(int32 flag, int32* cell) {
    if (flag > 0) {
        cell[0] = 1;
    }
    return 0;
}

int32 ensure_premise_caller(int32 count, int32* cell) {
    int32 status = set_when_positive(count, cell);
    return status;
}
```

```click
verifying "ensure_premise_flag.c";

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

int32 ensure_premise_caller(int32 count, int32* cell) {
    requires 1 <= count;
    owns cell[0..1];
    ensures cell[0] == 1;
} by {
    step();
    step();
    have cell[0] == 1 by {
        have count > 0 by {
            arithmetic() using {
                1 <= count;
            }
        }
        extract(cell[0] == 1);
        assumption();
    }
    execute();
    simp();
}
```

```expect
pass
```
