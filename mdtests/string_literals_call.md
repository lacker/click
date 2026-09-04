# String literal storage survives a function call

The literal's read-only byte storage belongs to the callee's function-level
state, but the returned pointer and its bytes remain valid in the caller.

```c filename=string_literals_call.c
uint8* literal_source() {
    return "ok";
}

int32 read_literal() {
    uint8* message;
    message = literal_source();
    return message[1];
}
```

```click
verifying "string_literals_call.c";

uint8* literal_source() {
    produces result[0..3];
    ensures result[0] == 'o';
    ensures result[1] == 'k';
    ensures result[2] == '\0';
} by {
    execute();
    simp();
}

int32 read_literal() {
    ensures result == 'k';
} by {
    execute();
    simp();
}
```

```expect
pass
```
