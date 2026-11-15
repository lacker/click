# A mark names a loop-head value after a long body

A failure report spells a value no current local holds as a local's value at
a recorded state. The loop below decrements `k` first and then runs forty
more statements, so no recent statement state holds the value `k` had at
the iteration's entry; the proof's `mark iteration` does. The report names
that value `at(iteration, k)` rather than `<unnamed A>`.

```c filename=a_mark_names_a_loop_head_value_after_a_long_body.c
int count_down(int n) {
    int k = n;
    int t = 0;
    while (k > 0) {
        k = k - 1;
        t = 0;
        t = 1;
        t = 2;
        t = 3;
        t = 4;
        t = 5;
        t = 6;
        t = 7;
        t = 8;
        t = 9;
        t = 10;
        t = 11;
        t = 12;
        t = 13;
        t = 14;
        t = 15;
        t = 16;
        t = 17;
        t = 18;
        t = 19;
        t = 20;
        t = 21;
        t = 22;
        t = 23;
        t = 24;
        t = 25;
        t = 26;
        t = 27;
        t = 28;
        t = 29;
        t = 30;
        t = 31;
        t = 32;
        t = 33;
        t = 34;
        t = 35;
        t = 36;
        t = 37;
        t = 38;
        t = 39;
    }
    return k;
}
```

```click
verifying "a_mark_names_a_loop_head_value_after_a_long_body.c";
int32 count_down(int32 n) {
    requires n >= 0;
    ensures result == 0;
} by {
    step_until(loop(0));
    loop {
        decreases k;
        invariant k >= 0;
        invariant k == n;
        preserve by {
            mark iteration;
            step_until(back_edge());
        }
    }
}
```

```expect
fail: to_integer(at(iteration, k) - 1) == n
```
