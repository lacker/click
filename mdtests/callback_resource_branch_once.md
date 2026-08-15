# callback resource handles branch-sensitive completion

This checks the natural callback control-flow pattern. Each path completes the
callback once: the failed path completes and returns early, while the success
path completes after the branch.

```c filename=complete.c
int32 complete(int32 cb) {
    return 0;
}
```

```c filename=complete_on_each_path.c
int32 complete_on_each_path(int32 cb, int32 failed) {
    int32 status;
    if (failed) {
        status = complete(cb);
        return 1;
    } else {
        status = 0;
    }
    status = complete(cb);
    return 0;
}
```

```click
abstract resource can_complete(cb: int32);

verifying "complete.c";
verifying "complete_on_each_path.c";

int32 complete(int32 cb) {
    consumes can_complete(cb);
}

int32 complete_on_each_path(int32 cb, int32 failed) {
    consumes can_complete(cb);

    ensures result == result by auto;
}
```

```expect
pass
```
