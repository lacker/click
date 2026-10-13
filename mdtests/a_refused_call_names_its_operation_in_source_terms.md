# A refused call names its operation in source terms

The `C operation` line of a refusal spells the call the way the C source
writes it, `first(s->data, s->len)`, and its call bindings name each
argument's field, not the lowered loads at the struct's byte offsets.

```c filename=a_refused_call_names_its_operation_in_source_terms.c
#include <stdint.h>
struct buf { uint64_t len; int32_t *data; };
int32_t first(int32_t *data, uint64_t len) { return data[0]; }
int32_t f(struct buf *s) { return first(s->data, s->len); }
```

```click
verifying "a_refused_call_names_its_operation_in_source_terms.c";
int32 first(int32* data, uint64 len) {
    requires 0u64 < len;
    views data[0..len];
} by { execute(); simp(); }
int32 f(struct buf* s) {
    views s->len;
    views s->data;
    requires 0u64 < s->len;
} by { execute(); simp(); }
```

```expect
fail: C operation: first(s->data, s->len)
  call bindings: data = s->data, len = s->len
```
