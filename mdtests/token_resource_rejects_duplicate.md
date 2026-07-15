# resource rejects duplicate token clauses

This checks that a token resource is not silently duplicated by writing
the same resource requirement twice.

```c filename=use_once.c
int32 use_once(int32 cb) {
    return 0;
}
```

```click
resource can_complete(cb: int32);

verifying "use_once.c";

int32 use_once(int32 cb) {
    consumes can_complete(cb);
    consumes can_complete(cb);

    ensures result == 0 by auto;
}
```

```expect
fail: duplicate resource fact `can_complete(cb)`
```
