# A `size_t` field in a pointer difference shows its `int64` reading

`end - b->content` is a `ptrdiff_t`, so the kernel adds `1` to the 64 bits
of `b->offset` read as `int64`. A 64-bit load carries no signedness, and
its place, the `size_t` field `b->offset`, states `uint64`. The goal
printed `old(b->offset) + 1i64`, which mixes the two types and does not say
which reading the sum uses. The field's operand now shows the conversion,
`old(b->offset) as int64 + 1i64`, which lowers back to the same term.

```c filename=a_size_t_field_in_a_pointer_difference_shows_its_int64_reading.c
#include <stddef.h>
typedef struct {
    const unsigned char *content;
    size_t length;
    size_t offset;
} parse_buffer;

size_t consumed(parse_buffer * const b) {
    const unsigned char *end = b->content + b->offset + 1;
    return (size_t)(end - b->content);
}
```

```click
verifying "a_size_t_field_in_a_pointer_difference_shows_its_int64_reading.c";
uint64 consumed(parse_buffer * const b) {
    views b->content;
    views b->length;
    views b->offset;
    requires b->content != 0;
    requires b->offset + 1 < b->length;
    requires b->length <= 9223372036854775807u64;
    views b->content[0..b->length];
    ensures result == b->offset + 1;
} by {
    have b->offset < b->length by { close(); }
    step();
    step();
    have to_integer(program::end - b->content) == 7 by { close(); }
}
```

```expect
fail: goal: to_integer(old(b->offset) as int64 + 1i64) == 7i64
```
