# resource rejects duplicate token at call site

This checks that a call cannot satisfy two resource parameters with the
same token. `consume_two` requires separate resources for `first` and `second`;
calling it as `consume_two(cb, cb)` tries to duplicate `can_complete(cb)`.

```c filename=consume_two.c
int32 consume_two(int32 first, int32 second) {
    return 0;
}
```

```c filename=call_same.c
int32 call_same(int32 cb) {
    int32 status;
    status = consume_two(cb, cb);
    return status;
}
```

```click
resource can_complete(cb: int32);

verifying "consume_two.c";
verifying "call_same.c";

int32 consume_two(int32 first, int32 second) {
    requires can_complete(first);
    requires can_complete(second);
}

int32 call_same(int32 cb) {
    requires can_complete(cb);

    ensures result == 0 by auto;
}
```

```expect
fail: duplicate resource `can_complete(cb)`
```
