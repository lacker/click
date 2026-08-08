# Repeated resource clauses require repeated units

Two equal resource clauses denote two units. They are valid together and are
both consumed by this contract.

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
pass
```
