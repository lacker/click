# resources cannot be minted by a contract

Several resource units may coexist, but a contract cannot duplicate one unit
without another resource law.

```c filename=duplicate_ref.c
int32 duplicate_ref(int32 object) {
    return object;
}
```

```click
abstract resource object_ref(object: int32);

verifying "duplicate_ref.c";

int32 duplicate_ref(int32 object) {
    owns object_ref(object);
    produces object_ref(object);

    ensures result == object by {
        execute();
    }
}
```

```expect
fail: did not establish every contract claim
```
