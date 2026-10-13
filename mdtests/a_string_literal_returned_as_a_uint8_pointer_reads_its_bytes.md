# A string literal returned as a `uint8 *` reads its bytes

Under the default x86_64-linux-userspace target plain `char` is signed, so a
string literal's `char *` and the declared `uint8 *` point to character types
of different signedness. GCC and Clang accept the uncast conversion with only
a `-Wpointer-sign` warning, and Click lowers it as the explicit
`(uint8 *)` cast: the caller reads the literal's bytes as unsigned bytes,
terminator included. Under x86_64-linux-kernel, where plain `char` is
unsigned, the same function verifies; see `string_literals.md`.

```c filename=a_string_literal_returned_as_a_uint8_pointer_reads_its_bytes.c
uint8* string_literal() {
    return "ok";
}
```

```click
verifying "a_string_literal_returned_as_a_uint8_pointer_reads_its_bytes.c";

uint8* string_literal() {
    ensures readable: viewable(result[0..3]);
    ensures first_byte: result[0] == 'o';
    ensures second_byte: result[1] == 107;
    ensures terminator: result[2] == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
