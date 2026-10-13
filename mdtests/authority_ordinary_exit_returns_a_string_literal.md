# A contract producing a string literal exits ordinarily

The entry state owns the function's own string literals. The contract
produces that storage and reaches no population, so it takes the ordinary
exit, which returns the body's resources, rather than composing the produced
literal onto a caller frame that already owns it.

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
target "x86_64-linux-kernel";
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
