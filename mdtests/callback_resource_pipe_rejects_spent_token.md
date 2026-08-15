# callback resource pipe rejects spent token

This checks the negative side of callback resource piping. The helper consumes
`can_complete(primary)` and only returns `can_complete(secondary)`, so the
caller cannot complete `primary` again afterward.

```c filename=complete.c
int32 complete(int32 cb) {
    return 0;
}
```

```c filename=complete_primary_and_secondary.c
int32 complete_primary_and_secondary(int32 primary, int32 secondary) {
    int32 status;
    status = complete(primary);
    return status;
}
```

```c filename=pipe_callback_bad.c
int32 pipe_callback_bad(int32 primary, int32 secondary) {
    int32 status;
    status = complete_primary_and_secondary(primary, secondary);
    status = complete(primary);
    return status;
}
```

```click
abstract resource can_complete(cb: int32);

verifying "complete.c";
verifying "complete_primary_and_secondary.c";
verifying "pipe_callback_bad.c";

int32 complete(int32 cb) {
    consumes can_complete(cb);
}

int32 complete_primary_and_secondary(int32 primary, int32 secondary) {
    consumes can_complete(primary);
    consumes can_complete(secondary);

    produces can_complete(secondary) by auto;
}

int32 pipe_callback_bad(int32 primary, int32 secondary) {
    consumes can_complete(primary);
    consumes can_complete(secondary);

    ensures result == 0 by auto;
}
```

```expect
fail: missing resource fact `owns can_complete(primary)`
```
