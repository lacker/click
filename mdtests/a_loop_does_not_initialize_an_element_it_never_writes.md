# a loop does not initialize an element it never writes

The negative next door to `mdtests/a_loop_keeps_a_local_array_initialized.md`.
The loop havoc keeps initialized the bytes whose cached values it forgets,
and nothing else: `a[2]` was written neither before the loop nor by it, so
reading it after the loop is a read of uninitialized storage.

```c filename=a_loop_does_not_initialize_an_element_it_never_writes.c
int32 after_loop() {
    int32 a[3];
    int32 i;
    a[0] = 5;
    a[1] = 5;
    i = 0;
    while (i < 2) {
        a[i] = 7;
        i = i + 1;
    }
    return a[2];
}
```

```click
verifying "a_loop_does_not_initialize_an_element_it_never_writes.c";

int32 after_loop() {
    ensures result == result;
} by {
    step();
    step();
    step();
    step();
    step();
    loop {
        decreases 2 - i;
        invariant i >= 0;
        invariant i <= 2;
    }
    step();
    close();
}
```

```expect
fail: undefined behavior: read of uninitialized storage
```
