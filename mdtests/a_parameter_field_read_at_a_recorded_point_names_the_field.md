# A parameter's field read at a recorded point names the field

A read at a recorded point, `at(statement(0).exit, b->offset)`, is spelled
against that point's locals. The parameter `b` is among them, and its local
entry carried only its kernel type, with no declaration and so no pointee
layout: the field printed as a typed read at a raw address,
`*(&b->offset as (int64 *))`, naming neither the field nor its `size_t`
type. A recorded point's locals keep the parameter's source declaration, as
the current state's do.

```c filename=a_parameter_field_read_at_a_recorded_point_names_the_field.c
#include <stddef.h>

typedef struct {
    const unsigned char *content;
    size_t length;
    size_t offset;
} parse_buffer;

void advance(parse_buffer * const b) {
    b->offset = 3;
    b->offset++;
}
```

```click
verifying "a_parameter_field_read_at_a_recorded_point_names_the_field.c";

void advance(parse_buffer * const b) {
    owns b->offset;
    ensures true;
} by {
    step();
    step();
    have b->offset == at(statement(0).exit, b->offset) + 5u64 by { close(); }
}
```

```expect
fail: goal: to_integer(b->offset) == to_integer(at(statement(0).exit, b->offset)) + 5
```
