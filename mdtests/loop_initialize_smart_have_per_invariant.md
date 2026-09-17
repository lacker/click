# A smart `have` inside `initialize by { ... }` is its invariant's own proof

An `initialize by { ... }` script that writes one `have` per declared
invariant names each invariant's proof individually. Before this fixture the
entry planner was handed the whole phase script as *every* invariant's proof,
so a smart `have` in it had no expansion of its own: `click verify` accepted
the sidecar while `click audit` failed the site with "Grouped proof has no
source tactic N", and the one expansion that was retained replaced the first
`have` with the certificate of the entire phase.

Each `have` below is now planned from its own body, so it expands to the same
`have` with a checked body, printed where it was written. `preserve by simp;`
is the same shape one phase over: a single smart tactic standing for the whole
phase, whose expansion is the planned preservation certificate.

```c filename=loop_initialize_smart_have_per_invariant.c
int spin(int n) {
    int i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "loop_initialize_smart_have_per_invariant.c";

int spin(int n) {
    requires n >= 0;
    ensures n >= 0;
} by {
    step();
    step();
    loop {
        invariant i >= 0;
        invariant i <= n;

        initialize by {
            have i >= 0 by simp;
            have i <= n by simp;
            assumption();
        }
        preserve by simp;
    }
    step();
    simp();
}
```

```termination
pending: unranked loop
```

```expect
pass
```
