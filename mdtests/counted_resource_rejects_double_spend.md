# one counted unit cannot satisfy two calls

Each consuming call spends one counted unit. A function which receives only
one unit cannot make two such calls.

```c filename=spend_ref.c
int32 spend_ref(int32 object) {
    return object;
}
```

```c filename=spend_ref_twice.c
int32 spend_ref_twice(int32 object) {
    int32 first = spend_ref(object);
    int32 second = spend_ref(object);
    return second;
}
```

```click
counted resource object_ref(object: int32);

verifying "spend_ref.c";
verifying "spend_ref_twice.c";

int32 spend_ref(int32 object) {
    consumes object_ref(object);

    ensures result == object by {
        execute();
    }
}

int32 spend_ref_twice(int32 object) {
    consumes object_ref(object);

    ensures result == object by {
        execute();
    }
}
```

```expect
fail: missing resource fact `owns object_ref(object)`
```
