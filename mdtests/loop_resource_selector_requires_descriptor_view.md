# A loop selector requires descriptor read authority

Owning the backing array through a separate pointer does not authorize reading
`h->data` to select that array at the loop head.

```c filename=probe.c
struct holder { int32* data; };
void probe(struct holder* h, int32* data, int32 n) {
    int32 i = 0;
    while (i < n) { h->data[i] = 1; i++; }
}
```
```click
verifying "probe.c";
resource cells(data: int32*, n: int32) { owns data[0..n]; }
void probe(struct holder* h, int32* data, int32 n) {
    requires 0 <= n;
    requires n <= 536870911;
    owns cells(data, n);
} by {
    step(); step();
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
fail: access outside the subobject the pointer designates
```
