# resource rejects wrong argument type

This checks that user-defined resource parameters are type checked. The
resource expects an `int32` callback id, but the contract passes an `int32*`.

```c filename=use_pointer.c
int32 use_pointer(int32* p) {
    return 0;
}
```

```click
resource can_complete(cb: int32);

verifying "use_pointer.c";

int32 use_pointer(int32* p) {
    consumes can_complete(p);

    ensures result == 0 by auto;
}
```

```expect
fail: resource `can_complete` argument 0 expects int32, got int32*
```
