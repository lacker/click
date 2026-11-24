# Loop guard paths may retain different proofs

The two entries to `a || b` prove `not a implies b` differently: the
`a` path refutes the premise, while the other path uses `b`. Both proofs
are valid and must remain associated with their guard-entry paths.
The loop is deliberately declared divergent so this tests certificate
merging without arithmetic or termination search.

```c filename=loop_guard_paths_keep_distinct_proofs.c
void guard_paths(bool a, bool b) {
    while (a || b) {}
}
```

```click
verifying "loop_guard_paths_keep_distinct_proofs.c";
void guard_paths(bool a, bool b) diverges {
    ensures true;
} by {
    loop diverges {
        invariant true;
        maintain by {
            have not a implies b by { close(); }
            step();
        }
    }
}
```

```expect
pass
```
