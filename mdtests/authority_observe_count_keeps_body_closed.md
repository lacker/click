# Observing a count does not say what the member's memory holds

Holding `permit(p)` lets C read `p[0]`, the memory the member owns, with or
without the observation. Observing its count adds nothing about the value
there, so the claim that the read returns zero is refused.

```c filename=observe_closed_body.c
int32 probe(int32* p) { return p[0]; }
```

```click
authorized resource permit(p: int32*) { owns p[0..1]; }
verifying "observe_closed_body.c";
int32 probe(int32* p) {
    owns authority(permit(p));
    owns permit(p);
    ensures result == 0;
} by {
    observe(permit(p));
    execute();
    simp();
}
```

```expect
fail: left side evaluated to old(p[0]), right side evaluated to 0
```
