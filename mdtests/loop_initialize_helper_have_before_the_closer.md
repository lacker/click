# A helper `have` in `initialize by { ... }` is written once, for the phase

A step written beside the invariant proofs in an `initialize by { ... }`
script is a helper: it establishes one standalone fact that the rest of the
phase reads. Before this fixture the whole script was handed to each
per-invariant entry planner, so expanding the closing `simp()` copied the
helper into every invariant's proof; `click verify` accepted the sidecar while
`click audit` failed the rewrite with "certificate failed round-trip
validation".

A leading run of `unfold` and non-invariant `have` steps is now planned once,
in written position, and its facts reach every invariant below. Expanding the
trailing `simp()` therefore leaves the helper where it was written and adds
one `have` per invariant after it.

```c filename=loop_initialize_helper_have_before_the_closer.c
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
verifying "loop_initialize_helper_have_before_the_closer.c";

int spin(int n) {
    requires n >= 0;
    ensures n >= 0;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0;
        invariant i <= n;

        initialize by {
            have n + 0 == n by { normalize(); }
            simp();
        }
        preserve by {
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
