# A string literal assigned to a `uint8 *` reads its bytes

The assignment form of
`a_string_literal_initializing_a_uint8_pointer_reads_its_bytes.md`: under the
default x86_64-linux-userspace target, assigning a string literal to a
`uint8 *` local without a cast is lowered as the explicit `(uint8 *)` cast,
which GCC and Clang accept with only a `-Wpointer-sign` warning.

```c filename=a_string_literal_assigned_to_a_uint8_pointer_reads_its_bytes.c
uint8* string_literal_assignment() {
    uint8* message;
    message = "ok";
    return message;
}
```

```click
verifying "a_string_literal_assigned_to_a_uint8_pointer_reads_its_bytes.c";

uint8* string_literal_assignment() {
    ensures readable: viewable(result[0..3]);
    ensures first_byte: result[0] == 111;
    ensures terminator: result[2] == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
