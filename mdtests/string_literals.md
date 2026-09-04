# C string literals provide stable read-only byte storage

C string literals lower to a byte array with one explicit terminating NUL.
The returned pointer remains usable through the existing `uint8[]` and
`cstr_len` proof interfaces.

```c filename=string_literals.c
uint8* string_literal() {
    return "ok";
}
```

```click
verifying "string_literals.c";

uint8* string_literal() {
    ensures readable: loadable(result[0..3]);
    ensures first_byte: result[0] == 'o';
    ensures terminator: result[2] == '\0';
} by {
    execute();
    simp();
}
```

```expect
pass
```
