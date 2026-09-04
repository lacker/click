# C string literals reject indirect writes

The literal is copied through a pointer local before the store. Read-only
storage must be enforced by the kernel memory block, so this remains invalid
even after the pointer loses its syntactic literal origin.

```c filename=string_literals_reject_write.c
uint8* string_literal_reject_write() {
    uint8* message;
    message = "ok";
    message[0] = 'x';
    return message;
}
```

```click
verifying "string_literals_reject_write.c";

uint8* string_literal_reject_write() {
    ensures result != 0;
} by {
    execute();
    simp();
}
```

```expect
fail: undefined behavior: invalid memory access
```
