# A loop selector cannot initialize an unwritten pointer field

The local descriptor is addressable and owned, but its pointer field has never
been initialized. Selecting a resource cannot invent its contents.

```c filename=probe.c
struct holder { int32* data; };
void probe(int32* data, int32 n) {
    struct holder holder;
    struct holder* h = &holder;
    int32 i = 0;
    while (i < n) { h->data[i] = 1; i++; }
}
```
```click
verifying "probe.c";
resource cells(data: int32*, n: int32) { owns data[0..n]; }
void probe(int32* data, int32 n) {
    requires 0 <= n;
    requires n <= 536870911;
    owns cells(data, n);
} by {
    step_until(loop(0).entry);
    loop {
        owns cells(h->data, n);
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        initialize by close();
        maintain by {
            unfold(cells(h->data, n));
            step(); step();
            fold(cells(h->data, n));
        }
    }
}
```
```expect
fail: could not establish that the memory location contains an initialized value
```
