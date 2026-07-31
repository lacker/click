# A point-local `have` proof rejects `advance`

`have ... by { ... }` opens a pure proof scope. Proof-level `if` is expanded
into logical cases there, but `advance` has region-join semantics that only
an execution proof can give it. A script that puts `advance` inside a `have`
must be reported, not replayed: the pure-proof replay assumes every
control-flow tactic was expanded away before it runs.

```c filename=joined_increment.c
int32 joined_increment(int32* p, int32 x) {
    int32 y;
    if (x >= 0) {
        y = x;
    } else {
        y = 0;
    }
    y = y + 1;
    return y;
}
```

```click
verifying "joined_increment.c";

int32 joined_increment(int32* p, int32 x) {
    requires x < 2147483647;
    owns p[0..1];

    ensures result > 0 by {
        execute_rest();
        have result > 0 by {
            advance(statement(1).exit)
            ensuring {
                fact y >= 0;
            }
            by {
                simp();
            }
            simp();
        };
        assumption();
    }
}
```

```expect
fail: `advance` is not available in a pure proof
```
