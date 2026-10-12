# Joining checked branch arms retains a call from either arm

```c filename=advance_nested_join.c
extern void may_spin(void);
int32 advance_nested_join(int32 x) {
    int32 y;
    if (x >= 0) {
        may_spin();
        y = x;
    } else {
        y = 0;
    }
    y = y + 1;
    return y;
}
```

```click
verifying "advance_nested_join.c";
extern void may_spin() diverges { ensures 1 == 1; }

int32 advance_nested_join(int32 x) {
    requires x < 2147483647;

    ensures result > 0 by {
        step();
        branch ensuring {
            fact y >= 0;
            fact y < 2147483647;
        } then {
            step();
            step();
        } else {
            step();
        }
        step();
        step();
        simp();
    }
}
```

```expect
fail: callee `may_spin` has no termination evidence
```
