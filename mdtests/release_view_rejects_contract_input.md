# A proof cannot release an ordinary contract input view

```c filename=release_input.c
int read(int *p) { int value = *p; return value; }
```

```click
verifying "release_input.c";

int32 read(int32* p) {
    views *p;
    ensures result == *p;
} by {
    step();
    release_view(*p);
    step_until(function.exit);
    close();
}
```

```expect
fail: release_view requires a produced view that holds a borrow
```
