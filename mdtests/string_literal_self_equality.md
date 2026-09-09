# A string literal occurrence compares equal to itself

The same literal pointer remains one object, even though two identical
occurrences may or may not share storage.

```c filename=string_literal_self_equality.c
int32 string_literal_self_equality() {
    uint8* value = "ok";
    if (value == value) {
        return 1;
    }
    return 0;
}
```

```click
verifying "string_literal_self_equality.c";

int32 string_literal_self_equality() {
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
