# Writing a private static needs ownership of it

A function that writes its file's private static without owning it fails
its implicit no-effect obligation, even when its postcondition names the
new value.

```c filename=library.c
struct counter { unsigned long value; };
static struct counter state = {7};
void reset(void) { state.value = 0; }
```

```click
verifying "library.c" as library;

void reset() {
    ensures library::state.value == 0u64;
} by { execute(); simp(); }
```

```expect
fail: outside the mutable footprint
```
