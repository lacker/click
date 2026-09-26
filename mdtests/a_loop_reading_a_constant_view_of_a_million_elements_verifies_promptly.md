# a loop reading a constant view of a million elements verifies promptly

The loop only reads the run seeded for `views a[0..1000000]`, so the loop head
keeps every element's entry value and `a[0]` after the loop is still its entry
value. Nothing here writes the range, so the work is independent of its
length.

```c filename=a_loop_reading_a_constant_view_of_a_million_elements_verifies_promptly.c
int32 scan_then_read(int32* a, int32 n) {
    int32 i;
    int32 found;
    i = 0;
    found = 0;
    while (i < n) {
        if (a[i] == 7) {
            found = 1;
        }
        i = i + 1;
    }
    return a[0];
}
```

```click
verifying "a_loop_reading_a_constant_view_of_a_million_elements_verifies_promptly.c";

int32 scan_then_read(int32* a, int32 n) {
    views a[0..1000000];
    requires 0 <= n;
    requires n <= 1000000;
    ensures result == a[0];
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
    }
    step();
    simp();
}
```

```expect
pass
```
