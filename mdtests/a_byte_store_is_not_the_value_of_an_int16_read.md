# a byte store is not the value of an `int16` read

The `int16` companion of
`a_byte_store_is_not_the_value_of_the_wide_read_it_lands_in.md`. `b[1] = 7`
writes the high byte of the `int16` at `q`, so `*q` reads `7 << 8` plus the
old low byte, never `7`. The read was **provable** as `7` because the walk
that resolves it stopped at the byte store and took the store's one-byte
value for the two-byte read.

```c filename=a_byte_store_is_not_the_value_of_an_int16_read.c
int32 need7(int32 x) {
    return x - 7;
}

int32 caller(int16* q) {
    unsigned char* b;
    int32 d;
    b = (unsigned char*)(void*) q;
    b[1] = 7;
    d = *q;
    return need7(d);
}
```

```click
verifying "a_byte_store_is_not_the_value_of_an_int16_read.c";

int32 need7(int32 x) {
    requires x == 7;
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 caller(int16* q) {
    owns q[0..1];
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: missing prerequisite (precondition clause 1 of `need7`)
```
