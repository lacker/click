# `witness` reports a frontier that has not reached function exit

`witness` introduces the binder for an existential ensures goal, which only
exists once execution has reached function exit. Used earlier it must be
reported against the tactic index, not resolved against a half-built
execution.

```c filename=pick.c
int32 pick(int32 x) {
    return x;
}
```

```click
verifying "pick.c";

int32 pick(int32 x) {
    requires x >= 0;

    ensures exists: (0..1).any(|k| result == x) by {
        witness(k = 0);
        execute_rest();
        simp();
    }
}
```

```expect
fail: `witness` requires execution to reach function exit first
```
