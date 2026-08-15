# callback resource can be completed once

This checks the protocol-only function shape. `complete(cb)` consumes
`can_complete(cb)` and does not return it. A caller that invokes it once can
still prove an ordinary postcondition afterward.

```c filename=complete.c
int32 complete(int32 cb) {
    return 0;
}
```

```c filename=complete_once.c
int32 complete_once(int32 cb) {
    int32 status;
    status = complete(cb);
    return 0;
}
```

```click
abstract resource can_complete(cb: int32);

verifying "complete.c";
verifying "complete_once.c";

int32 complete(int32 cb) {
    consumes can_complete(cb);
}

int32 complete_once(int32 cb) {
    consumes can_complete(cb);

    ensures result == 0 by auto;
}
```

```expect
pass
```
