# a loop writing a seeded constant range does not keep its entry values

The loop writes elements of the run seeded for `owns a[0..1000000]`, so the
loop head keeps none of the run's entry values, and `a[0]` after the loop is
not its entry value: `result == old(a[0])` is refused. The C returns `0`
whenever `n > 0`.

```c filename=a_loop_over_a_constant_range_does_not_keep_its_entry_values.c
int32 clear_then_read(int32* a, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        a[i] = 0;
        i = i + 1;
    }
    return a[0];
}
```

```click
verifying "a_loop_over_a_constant_range_does_not_keep_its_entry_values.c";

int32 clear_then_read(int32* a, int32 n) {
    owns a[0..1000000];
    requires 0 <= n;
    requires n <= 1000000;
    ensures result == old(a[0]);
} by {
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
fail: result == old(a[0])
```
