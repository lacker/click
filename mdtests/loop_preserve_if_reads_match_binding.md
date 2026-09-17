# A preservation `if` can read its enclosing `match` binding

A proof `match` inside a loop-preservation body introduces constructor fields
as lexical bindings. A nested proof-level `if` must lower its condition in
that same scope. Both arms below execute the same loop-body statement, so the
only distinction is whether the condition can name `end`.

```c filename=loop_preserve_if_reads_match_binding.c
void count_to(int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
}
```

```click
verifying "loop_preserve_if_reads_match_binding.c";

spec enum Bound { At(int32) }

resource marker() {
    field model: Bound;
    match model {
        Bound::At(end) => { fact end >= 0; },
    }
}

void count_to(int32 n) {
    requires n >= 0;
    owns m: marker();
    ensures m.model == old(m.model);
} by {
    step();
    step();
    loop {
        owns m: marker();
        decreases n - i;
        invariant i >= 0;
        invariant i <= n;
        invariant m.model == old(m.model);

        initialize by simp;
        preserve by {
            have 0 <= n - i - 1 by { arithmetic() using { i < n; i >= 0; n >= 0; } }
            have n - i - 1 < n - i by { arithmetic() using { i < n; i >= 0; n >= 0; } }
            match m.model {
                Bound::At(end) => {
                    if i < end {
                        step();
                        close_invariants();
                    } else {
                        step();
                        close_invariants();
                    }
                },
            }
        }
    }
    step();
    simp();
}
```

```expect
pass
```
