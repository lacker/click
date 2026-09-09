# A returned pointer cannot expose an automatic object after function exit

The pointer value survives the return expression, but the automatic object it
points to does not. A postcondition must not read that ended lifetime.

```c filename=returned_local_postcondition.c
int32* returned_local_postcondition_rejected() {
    int32 value = 5;
    return &value;
}

int32* return_input(int32* input) {
    return input;
}
```

```click
verifying "returned_local_postcondition.c";

int32* returned_local_postcondition_rejected() {
    ensures result[0] == 5;
}

int32* return_input(int32* input) {
    requires loadable(input[0..1]);
    ensures result[0] == input[0];
}
```

```expect
fail: unverified claims
```
