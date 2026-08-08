# counted resources cannot be minted by a contract

Declaring a resource counted permits several units to coexist; it does not
permit one unit to be duplicated without another resource law.

```c filename=duplicate_ref.c
int32 duplicate_ref(int32 object) {
    return object;
}
```

```click
counted resource object_ref(object: int32);

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
