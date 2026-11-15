# Resource viewability remembers its state

```c filename=dispose.c
void dispose(int32 *p) { free(p); }
```

```click
abstract resource token(id: int32);
verifying "dispose.c";
void dispose(int32 *p) {
    requires viewable(token(0));
    consumes allocation(p, 4);
    consumes p[0..1];
    ensures at(function.entry, viewable(token(0))) by {
        step();
        step();
        known();
    }
    ensures at(function.entry, viewable(memory(p[0..1]))) by {
        step();
        step();
        known();
    }
}
```

```expect
pass
```
