# A word read through an `unsigned int *` is not its signed value

The `int` `-1` read through an `unsigned int *` is `4294967295`. A
claim that the read returns the signed value `-1` as an `int64` is false.

```c filename=a_word_read_through_an_unsigned_int_pointer_is_not_its_signed_value.c
long long read_unsigned_word(void) {
    int x = -1;
    unsigned int *q = &x;
    return *q;
}
```

```click
verifying "a_word_read_through_an_unsigned_int_pointer_is_not_its_signed_value.c";

int64 read_unsigned_word() { ensures result == -1 by auto; }
```

```expect
fail: unclosed goal
```
