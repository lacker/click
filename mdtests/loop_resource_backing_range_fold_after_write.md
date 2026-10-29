# A loop resource can select its backing through a framed descriptor field
```c filename=probe.c
struct holder { int32* data; };
void probe(struct holder* h, int32 n) {
    int32 i = 0;
    while (i < n) { h->data[i] = 1; i++; }
}
```
```click
verifying "probe.c";
resource cells(data: int32*, n: int32) { owns data[0..n]; }
void probe(struct holder* h, int32 n) {
    requires 0 <= n;
    requires n <= 536870911;
    views h->data;
    owns cells(h->data, n);
} by {
    step(); step();
    loop {
        owns cells(h->data, n);
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        initialize by solve();
        preserve by {
            unfold(cells(h->data, n));
            have separate(memory(h->data), memory(h->data[i]));
            step(); step();
            fold(cells(h->data, n));
            close_invariants();
        }
    }
}
```
```expect
pass
```
