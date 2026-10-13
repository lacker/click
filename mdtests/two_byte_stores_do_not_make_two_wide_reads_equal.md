# two byte stores do not make two wide reads equal

Both reads of `*q` follow a store of `7` to its high byte, but the low byte
differs between them: the first read keeps the caller's, the second keeps
`y`'s. So `d1 == d2` holds only when those low bytes agree.

It was **provable** for every `y`. Each read resolved to the value of the
byte store it stopped at, both were `7`, and `same`'s precondition
`d1 == d2` became `7 == 7`. The byte store is not either read's value;
`a_byte_store_is_not_the_value_of_the_wide_read_it_lands_in.md` states the
rule.

```c filename=two_byte_stores_do_not_make_two_wide_reads_equal.c
int32 same(int32 a, int32 b) {
    return 0;
}

int32 two_reads(int16* q, int16 y) {
    unsigned char* b;
    int32 d1;
    int32 d2;
    b = (unsigned char*)(void*) q;
    b[1] = 7;
    d1 = *q;
    *q = y;
    b[1] = 7;
    d2 = *q;
    return same(d1, d2);
}
```

```click
verifying "two_byte_stores_do_not_make_two_wide_reads_equal.c";

int32 same(int32 a, int32 b) {
    requires a == b;
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 two_reads(int16* q, int16 y) {
    owns q[0..1];
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: missing prerequisite (precondition clause 1 of `same`)
```
