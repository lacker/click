# a loop writing a long global array does not keep its entry values

A function's entry names every element of a global array it knows nothing
about as one run of cells, whatever the array's length. The loop writes
elements of that run, so the loop head keeps none of its entry values, and
`buf[0]` after the loop is not its entry value. The C returns `0` whenever
`n > 0`.

```c filename=a_loop_over_a_long_global_array_does_not_keep_its_entry_values.c
int32 buf[1000];

int32 clear_then_read(int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        buf[i] = 0;
        i = i + 1;
    }
    return buf[0];
}
```

```click
verifying "a_loop_over_a_long_global_array_does_not_keep_its_entry_values.c";

int32 clear_then_read(int32 n) {
    owns buf[0..1000];
    requires 0 <= n;
    requires n <= 1000;
    ensures result == old(buf[0]);
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
    }
    step();
    close();
}
```

```expect
fail: result == old(buf[0])
```
