# a signed read of a byte follows from its unsigned read

One byte, one name: a byte's single term is its unsigned read, and a
`signed char` read of it is the two's-complement conversion of that term.
So a fact about the unsigned read decides the signed one. Here the contract
states the byte as `unsigned char` (`u[i] == 255`, and `u[i] == 5`) and the
body reads it through a `signed char*` view of the same storage, which
returns -1 and 5. Before, the two reads were unrelated unknowns and neither
claim was provable. `a_signed_and_an_unsigned_byte_read_are_two_values.md`
keeps the refusal that the two reads are the same number.

```c filename=a_signed_read_of_a_byte_follows_from_its_unsigned_read.c
int read_high(unsigned char* u, int i) {
    signed char* s;
    s = (signed char*)(void*) u;
    return s[i];
}

int read_low(unsigned char* u, int i) {
    signed char* s;
    s = (signed char*)(void*) u;
    return s[i];
}
```

```click
verifying "a_signed_read_of_a_byte_follows_from_its_unsigned_read.c";

int read_high(unsigned char* u, int i) {
    requires i >= 0;
    requires i < 4;
    views u[0..4];
    requires u[i] == 255;
    ensures result == -1;
} by {
    execute();
    simp();
}

int read_low(unsigned char* u, int i) {
    requires i >= 0;
    requires i < 4;
    views u[0..4];
    requires u[i] == 5;
    ensures result == 5;
} by {
    execute();
    simp();
}
```

```expect
pass
```
