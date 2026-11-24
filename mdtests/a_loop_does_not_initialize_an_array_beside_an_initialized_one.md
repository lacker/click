# a loop does not initialize an array beside an initialized one

The negative next door to
`mdtests/a_loop_keeps_an_initialized_automatic_array_initialized.md`. The
declaration `int32 a[4] = {1};` records all of `a` initialized, and the loop
that writes `a[i]` keeps it so. Nothing ever wrote `b[3]`, and neither the
declaration of `a` nor the loop records any byte of `b`: reading it after the
loop is a read of uninitialized storage.

```c filename=a_loop_does_not_initialize_an_array_beside_an_initialized_one.c
int32 after_loop() {
    int32 a[4] = {1};
    int32 b[4];
    int32 i;
    b[0] = 1;
    i = 0;
    while (i < 2) {
        a[i] = 7;
        b[i] = 7;
        i = i + 1;
    }
    return b[3];
}
```

```click
verifying "a_loop_does_not_initialize_an_array_beside_an_initialized_one.c";

int32 after_loop() {
    ensures result == result;
} by {
    step();
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
