# byte-slice standard library helpers

This checks the first byte-slice prelude layer over `uint8[]` arrays. The
helpers use explicit half-open ranges or offset+length slices, not
null-terminated C strings.

```c filename=count_byte3.c
int32 count_byte3(uint8 p[], uint8 x) {
    int32 count;
    count = 0;
    if (p[0] == x) {
        count = count + 1;
    } else {
        count = count;
    }
    if (p[1] == x) {
        count = count + 1;
    } else {
        count = count;
    }
    if (p[2] == x) {
        count = count + 1;
    } else {
        count = count;
    }
    return count;
}
```

```c filename=byte_slice_facts.c
int32 byte_slice_facts(uint8 p[], uint8 q[]) {
    return 0;
}
```

```click
verifying "count_byte3.c";
verifying "byte_slice_facts.c";

int32 count_byte3(uint8 p[], uint8 x) {
    requires valid_range(p[0..3]);
    requires read(p[0..3]);
    ensures stdlib_byte_count_value: result == byte_count(p, 0, 3, x) by auto;
}

int32 byte_slice_facts(uint8 p[], uint8 q[]) {
    requires valid_range(p[0..3]);
    requires valid_range(q[0..2]);
    requires shifted_equal: bytes_equal(p, 1, q, 0, 2);
    requires all_q_are_a: bytes_all_eq(q, 0, 2, 'a');

    ensures shifted_second_equal: p[2] == q[1] by {
        symbolic_execute();
        unfold(bytes_equal);
        simp();
    }

    ensures first_q_is_a: q[0] == 'a' by {
        symbolic_execute();
        unfold(bytes_all_eq);
        simp();
    }

    ensures current_equals_old: bytes_equal_range(p, old(p), 0, 3) by {
        symbolic_execute();
        unfold(bytes_equal_range);
        simp();
    }
}
```

```expect
pass
```
