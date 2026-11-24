# A deferred match arm cannot assume an arbitrary payload value

```c filename=scope.c
int read(int* p) { return *p; }
```

```click
verifying "scope.c";
spec enum Tri { Zero, One, Other(int) }
resource cell(p: int*) { field model: Tri; owns p[0..1]; }
int read(int* p) {
    owns c: cell(p);
    ensures result == p[0];
    ensures c.model == old(c.model);
} by {
    step_until(function.exit);
    match old(c.model) {
        Tri::Zero => { close(); },
        Tri::One => { close(); },
        Tri::Other(payload) => {
            have payload == 0;
            cases {
                payload == 0 => { close(); }
                payload != 0 => { close(); }
            }
        },
    }
}
```

```expect
fail: could not establish `payload == 0`
```
