# One resource unit cannot satisfy a two-unit call

This checks that a call cannot satisfy two resource parameters with the
same token. `consume_two(cb, cb)` requires quantity two of
`can_complete(cb)`, while its caller owns only quantity one.

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
abstract resource can_complete(cb: int32);

verifying "consume_two.c";
verifying "call_same.c";

int32 consume_two(int32 first, int32 second) {
    consumes can_complete(first);
    consumes can_complete(second);
}

int32 call_same(int32 cb) {
    consumes can_complete(cb);

    ensures result == 0 by auto;
}
```

```expect
fail: missing resource fact `owns can_complete(cb) (quantity 2)`
```
