# A string literal initializing a `uint8 *` reads its bytes

Under the default x86_64-linux-userspace target plain `char` is signed, so
initializing a `uint8 *` local from a string literal without a cast converts
between pointers to character types of different signedness. GCC and Clang
accept it with only a `-Wpointer-sign` warning, and Click lowers it as the
explicit `(uint8 *)` cast, so reads through the local see the literal's bytes.

```c filename=a_string_literal_initializing_a_uint8_pointer_reads_its_bytes.c
int32 string_literal_initializer() {
    uint8* first = "ok";
    return first[0] == 'o';
}

uint8* string_literal_initialized_pointer() {
    uint8* first = "ok";
    return first;
}
```

```click
verifying "a_string_literal_initializing_a_uint8_pointer_reads_its_bytes.c";

int32 string_literal_initializer() {
    ensures result == 1;
} by {
    execute();
    simp();
}

uint8* string_literal_initialized_pointer() {
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
