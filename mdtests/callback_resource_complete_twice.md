# callback resource rejects double completion

This checks the guiding synthetic-resource example: `can_complete(cb)` is an
resource right to call `complete(cb)`. The first call consumes the token, so the
second call is rejected.

```c filename=complete.c
int32 complete(int32 cb) {
    return 0;
}
```

```c filename=complete_twice.c
int32 complete_twice(int32 cb) {
    int32 status;
    status = complete(cb);
    status = complete(cb);
    return 0;
}
```

```click
resource can_complete(cb: int32);

verifying "complete.c";
verifying "complete_twice.c";

int32 complete(int32 cb) {
    requires can_complete(cb);
}

int32 complete_twice(int32 cb) {
    requires can_complete(cb);

    ensures result == 0 by auto;
}
```

```expect
fail: missing resource fact `can_complete(cb)`
```
