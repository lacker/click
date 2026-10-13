# A signed char fact does not give another unsigned byte

`p[0] == 7` on a user-space (signed) `char` decides the unsigned byte read
through `(unsigned char *)p` as 7
(`userspace_signed_char_fact_decides_the_unsigned_byte.md`). It decides
nothing else: `135` is the unsigned byte of no `char` equal to 7 (it is
`-121`), so this claim is refused rather than read off a different byte.

```c filename=signed_char_fact_does_not_give_another_unsigned_byte.c
int first_unsigned(char *p) {
    return ((unsigned char *)p)[0];
}
```

```click
target "x86_64-linux-userspace";
verifying "signed_char_fact_does_not_give_another_unsigned_byte.c";

int32 first_unsigned(char* p) {
    views p[0..1];
    requires p[0] == 7;
    ensures result == 135;
} by {
    execute();
    simp();
}
```

```expect
fail: `ensures result == 135` failed for `first_unsigned.ensures_0`
```
