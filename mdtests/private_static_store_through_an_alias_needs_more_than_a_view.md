# A store through an argument that may alias a viewed private static is refused

The helper owns `p->value` and only views the private static. `p` may be
the static's address, so the store is not shown separate from the view and
is refused instead of assuming the two do not alias.

```c filename=library.c
struct counter { unsigned long value; };
static struct counter state = {7};
unsigned long set_then_read(struct counter *p) { p->value = 5; return state.value; }
unsigned long next(void) { return set_then_read(&state); }
```

```click
verifying "library.c" as library;

unsigned long set_then_read(struct counter *p) {
    owns p->value;
    views library::state.value;
    ensures result == 5u64;
} by { execute(); simp(); }
```

```expect
fail: could not prove the requested ranges separate
```
