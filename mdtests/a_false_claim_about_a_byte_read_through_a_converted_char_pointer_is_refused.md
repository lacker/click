# A false claim about a byte read through a converted `char *` is refused

The negative form of
`a_uint8_pointer_passed_as_a_char_pointer_reads_signed_bytes.md`. Under the
default x86_64-linux-userspace target, a `uint8 *` passed uncast to a `char *`
parameter is read as signed bytes, so the byte `0xC8` reads as `-56`, and a
claim that the callee sees its unsigned value `200` is refused.

```c filename=a_false_claim_about_a_byte_read_through_a_converted_char_pointer_is_refused.c
int first_char(char *p) { return p[0]; }

int pass_pointer(void) {
    uint8 buf[2];
    uint8 *q = buf;
    buf[0] = 200;
    buf[1] = 0;
    return first_char(q);
}
```

```click
verifying "a_false_claim_about_a_byte_read_through_a_converted_char_pointer_is_refused.c";

int first_char(char *p) {
    views p[0..1];
    ensures result == p[0] by auto;
}
int pass_pointer() { ensures result == 200 by auto; }
```

```expect
fail: unclosed goal
```
