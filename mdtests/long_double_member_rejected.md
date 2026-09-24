# Opaque `long double` fields cannot be read as byte arrays

The ABI layout can be imported, but a member read must wait for a typed
extended-precision value model.

```c filename=long_double_member_rejected.c
struct Box {
    long double value;
};

int32 inspect(struct Box *box) {
    return (int32)box->value;
}
```

```click
verifying "long_double_member_rejected.c";

int32 inspect(struct Box *box) {
    ensures result == 0 by auto;
}
```

```expect
fail: long double member value operations need an extended-precision model
```
