# callback resource rejects branch double completion

This checks a path-sensitive double-completion bug. The second `complete(cb)`
is only invalid on the path where the branch already consumed
`can_complete(cb)`, and Click reports the missing resource fact.

```c filename=complete.c
int32 complete(int32 cb) {
    return 0;
}
```

```c filename=complete_maybe_twice.c
int32 complete_maybe_twice(int32 cb, int32 failed) {
    int32 status;
    if (failed) {
        status = complete(cb);
    } else {
        status = 0;
    }
    status = complete(cb);
    return 0;
}
```

```click
resource can_complete(cb: int32);

verifying "complete.c";
verifying "complete_maybe_twice.c";

int32 complete(int32 cb) {
    consumes can_complete(cb);
}

int32 complete_maybe_twice(int32 cb, int32 failed) {
    consumes can_complete(cb);

    ensures result == 0 by auto;
}
```

```expect
fail: missing resource fact `owns can_complete(cb)`
```
