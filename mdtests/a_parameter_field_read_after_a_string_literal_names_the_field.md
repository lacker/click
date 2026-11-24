# A parameter's field read after a string literal names the field

`sizeof("")` gives the function storage for the literal, and its
initializing store moves the memory a later read sees off function entry.
Reads of `b->offset` are then spelled against the current state's locals.
That naming held the parameter `b` with only its kernel type: no
declaration, so no pointee layout. Its fields printed as typed reads at raw
addresses, `at(<state A>, *(&b[4] as (int64 *)))`, which names neither
the field nor its `size_t` type. A state local that is a parameter keeps
the parameter's source declaration, so the goal names `b->offset`. The same
read without the literal is `old(b->offset)`.

```c filename=a_parameter_field_read_after_a_string_literal_names_the_field.c
#include <stddef.h>

typedef struct {
    const unsigned char *content;
    size_t length;
    size_t offset;
} parse_buffer;

int peek(parse_buffer * const b) {
    size_t terminator = sizeof("");
    const unsigned char *p = b->content + b->offset;
    return p[0] + (int)terminator;
}
```

```click
verifying "a_parameter_field_read_after_a_string_literal_names_the_field.c";

int32 peek(parse_buffer * const b) {
    views b->content;
    views b->length;
    views b->offset;
    let content = b->content;
    let length = b->length;
    let offset = b->offset;
    requires offset < length;
    views content[0..length];
    ensures result == content[offset] + 1;
} by {
    step();
    have b->offset == 7u64 by { close(); }
}
```

```expect
fail: goal: at(<state A>, b->offset) == 7u64
```
