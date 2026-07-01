# callback resource can pipe one callback through another

This checks that exact-match affine resources can be transferred through helper
contracts. `complete_primary_and_secondary` consumes the primary callback token
and returns the secondary callback token, so the caller can complete the
secondary callback afterward but cannot complete the primary callback again.

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

```c filename=pipe_callback.c
int32 pipe_callback(int32 primary, int32 secondary) {
    int32 status;
    status = complete_primary_and_secondary(primary, secondary);
    status = complete(secondary);
    return status;
}
```

```click
affine resource can_complete(cb: int32);

verifying "complete.c";
verifying "complete_primary_and_secondary.c";
verifying "pipe_callback.c";

int32 complete(int32 cb) {
    requires can_complete(cb);
}

int32 complete_primary_and_secondary(int32 primary, int32 secondary) {
    requires can_complete(primary);
    requires can_complete(secondary);

    ensures can_complete(secondary) by auto;
}

int32 pipe_callback(int32 primary, int32 secondary) {
    requires can_complete(primary);
    requires can_complete(secondary);

    ensures result == 0 by auto;
}
```

```expect
pass
```
