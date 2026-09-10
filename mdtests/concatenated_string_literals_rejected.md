# Unsupported escapes remain rejected in concatenated C string literals

Concatenation does not broaden the set of supported literal escapes.

```c filename=concatenated_string_literals_rejected.c
uint8* invalid_string() {
    return "hello" "\x20world";
}
```

```click
verifying "concatenated_string_literals_rejected.c";

uint8* invalid_string() {
    ensures result != 0;
} by {
    execute();
    simp();
}
```

```expect
fail: unsupported string escape
```
