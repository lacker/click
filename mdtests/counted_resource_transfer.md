# counted resources transfer one unit at a time

A counted resource can occur more than once in a resource context. Calls consume
one unit per contract clause, leaving the other units available for later calls.

```c filename=counted_resource_transfer.c
int32 drop_ref(int32 object) {
    return object;
}
```

```c filename=use_counted_resource.c
int32 use_ref(int32 object) {
    return object;
}
```

```c filename=use_two_refs.c
int32 use_two_refs(int32 object) {
    int32 ignored = drop_ref(object);
    int32 result = use_ref(object);
    return result;
}
```

```c filename=package_one_ref.c
int32 package_one_ref(int32 object) {
    return object;
}
```

```click
counted resource object_ref(object: int32);

resource held_ref(object: int32) {
    contains object_ref(object);
}

verifying "counted_resource_transfer.c";
verifying "use_counted_resource.c";
verifying "use_two_refs.c";
verifying "package_one_ref.c";

int32 drop_ref(int32 object) {
    consumes object_ref(object);

    ensures result == object by {
        execute();
    }
}

int32 use_ref(int32 object) {
    consumes object_ref(object);

    ensures result == object by {
        execute();
    }
}

int32 use_two_refs(int32 object) {
    consumes object_ref(object);
    consumes object_ref(object);

    ensures result == object by {
        execute();
    }
}

int32 package_one_ref(int32 object) {
    consumes object_ref(object);
    owns object_ref(object);

    produces held_ref(object) by {
        execute();
        fold(held_ref(object));
    }
}

```

```expect
pass
```
