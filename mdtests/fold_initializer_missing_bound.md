# A fold initializer cannot omit its overflow prerequisite

A field initializer's evaluation domain is an ordinary fold obligation.
Its written proof must be accepted even when the ambient bound lets solve
establish the domain immediately.

```c filename=fold_initializer_obligation.c
void make(int32 n) {}
```

```click
verifying "fold_initializer_obligation.c";
resource counter() {
    field next: int32;
}
void make(int32 n) {
    produces c: counter();
} by {
    let c = fold(counter(), { next: n + 1 }) by { close(); }
}
```

```expect
fail: `have` failed for
```
