# A constant range bound is not named by a local holding it

`skipped` holds `0`, and the view's lower bound is the constant `0u64`.
A report spelled the bound by the first local or parameter whose value
equals it, so the range printed as `b->content[skipped..b->length]`: a
different fact from the one written, which would change meaning as soon as
`skipped` did. A constant is spelled as its literal.

```c filename=a_constant_range_bound_is_not_named_by_a_local_holding_it.c
#include <stddef.h>

typedef struct {
    const unsigned char *content;
    size_t length;
} parse_buffer;

size_t mark(parse_buffer * const b, unsigned char *out) {
    size_t skipped = 0;
    *out = 0;
    return skipped;
}
```

```click
verifying "a_constant_range_bound_is_not_named_by_a_local_holding_it.c";

uint64 mark(parse_buffer * const b, uint8* out) {
    views b->content;
    views b->length;
    owns out[0..1];
    views b->content[0..b->length];
    ensures true;
} by {
    step();
    step();
    step();
    have separate(memory(out[0..2]), memory(b->content[0u64..b->length])) by { close(); }
}
```

```expect
fail: goal: separate(out[0..2], b->content[0u64..b->length])
```
