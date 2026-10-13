# A const private static cast for a writing helper is refused

A wrapper casts away the const of its private static to pass it to a
helper that writes through its argument. The helper's mutable footprint
would cover read-only storage, so the call is refused.

```c filename=library.c
struct counter { unsigned long value; };
static const struct counter limit = {7};
void reset(struct counter *p) { p->value = 0; }
void reset_limit(void) { reset((struct counter *)&limit); }
```

```click
verifying "library.c" as library;

void reset(struct counter *p) {
    owns p->value;
    ensures p->value == 0u64;
} by { execute(); simp(); }

void reset_limit() {
    owns library::limit.value;
    ensures library::limit.value == 0u64;
} by { execute(); simp(); }
```

```expect
fail: mutable footprint covers read-only storage
```
