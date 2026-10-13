# A helper cannot own a private static and the argument that aliases it

A wrapper passes its private static to a helper that owns both its
argument's field and the static itself. The two resources are one object,
so the call is refused rather than duplicating ownership.

```c filename=library.c
struct counter { unsigned long value; };
static struct counter state = {7};
unsigned long bump(struct counter *p) { p->value += 1; return state.value; }
unsigned long next(void) { return bump(&state); }
```

```click
verifying "library.c" as library;

unsigned long bump(struct counter *p) {
    requires p->value < 100u64;
    owns p->value;
    owns library::state.value;
    ensures result == library::state.value;
} by { execute(); simp(); }

unsigned long next() {
    requires library::state.value < 100u64;
    owns library::state.value;
    ensures result == library::state.value;
} by { execute(); simp(); }
```

```expect
fail: overlapping owned memory resource facts
```
