# epoch attack 3: a loop that writes the array

The loop stores `1` into every cell of `a[0..n]`, so across it the array
changes.

The fact carries content: `icount(a, 0, 1) == 5` comes from
`requires a[0] == 5` through the fold's defining equation, and it reads
`a[0]`, which the first iteration overwrites with `1` whenever `0 < n`, so
after the loop it is false. An empty-range fact would say nothing here: it is
true across any write, and the checked fold read frame carries it.

```c filename=array_fact_does_not_survive_a_loop_that_writes_it.c
void wipe(int32 a[], int32 n) {
    for (int32 i = 0; i < n; i++) {
        a[i] = 1;
    }
}
```

```click
verifying "array_fact_does_not_survive_a_loop_that_writes_it.c";

function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

void wipe(int32 a[], int32 n) {
    requires 0 < n;
    requires n <= 1073741823;
    requires a[0] == 5;
    consumes a[0..n];
    produces a[0..n];
} by {
    step();
    have 0 <= 0 by { simp(); }
    have icount(a, 0, 0) == 0 by {
        unfold(icount(a, 0, 0)) using { 0 <= 0; }
        normalize();
    }
    have to_integer(a[0]) == 5 by { simp() using { a[0] == 5; }; }
    have icount(a, 0, 1) == 5 by {
        unfold(icount(a, 0, 1)) using { 0 <= 0; 0 < 2147483647; }
        arithmetic() using { icount(a, 0, 0) == 0; to_integer(a[0]) == 5; }
    }
    step();
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        owns a[0..n];
        initialize by { simp(); }
        preserve by {
            step();
            step();
            close_invariants();
        }
    }
    have icount(a, 0, 1) == 5 by { simp(); }
    execute();
    simp();
}
```

```expect
fail: a fact about `a` as a whole does not carry across the loop. Only a step the kernel proves leaves the whole object alone carries one, and a stated `separate(...)` is not read here.
```
