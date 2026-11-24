# A call cannot write its viewed private static

The helper proves preservation using the separation in its ownership/view
partition. The caller cannot satisfy that partition when its owned argument
is the same private static the helper views.

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
    ensures library::state.value == old(library::state.value);
} by {
    have separate(memory(p->value), memory(library::state.value)) by { close(); }
}
unsigned long next() {
    owns library::state.value;
    requires library::state.value == 7u64;
    ensures result == 7u64;
}
```

```expect
fail: A required resource overlaps a live borrow.
```
