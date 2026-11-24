# An earlier viewability fact cannot make released memory viewable now

```c filename=dispose.c
void dispose(int32 *p) { free(p); }
```

```click
verifying "dispose.c";
void dispose(int32 *p) {
    consumes allocation(p, 4);
    consumes p[0..1];
    ensures viewable(memory(p[0..1])) by {
        step();
        step();
        close();
    }
}
```

```expect
fail: `ensures viewable(memory(p[0..1]))` failed for `dispose.ensures_0` path 0
```
