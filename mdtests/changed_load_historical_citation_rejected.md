# A historical load does not justify an unqualified current load

This is the direct-citation companion to
`resource_match_quantified_fact_rejects_changed_load.md`. The entry fact is
valid at its original snapshot, but `p[0]` in the proof after the store means
the new C state. A presentation record for the older fact cannot substitute
for the current proposition.

```c filename=changed_load_historical_citation_rejected.c
int32 change(int32 p[]) {
    p[0] = 1;
    return 0;
}
```

```click
verifying "changed_load_historical_citation_rejected.c";

int32 change(int32 p[]) {
    consumes p[0..1];
    requires p[0] == 0;
    ensures result == 0;
} by {
    step();
    have p[0] == 0 by { assumption(); }
    step();
    simp();
}
```

```expect
fail: requires the current goal as an available semantic fact
```
