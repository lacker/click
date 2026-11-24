# Changing a descriptor does not retarget its owned backing resource

The loop can change `h->data`, so its abstract head cannot retain the entry
selector while framing the backing owner. Owning the descriptor permits writes;
it does not transfer the backing resource to the new pointer.

```c filename=probe.c
struct holder { int32* data; };
void probe(struct holder* h, int32 n) {
    int32 i = 0;
    while (i < n) { h->data[i] = 1; h->data = 0; i++; }
}
```
```click
verifying "probe.c";
resource cells(data: int32*, n: int32) { owns data[0..n]; }
void probe(struct holder* h, int32 n) {
    requires 0 <= n;
    requires n <= 536870911;
    owns h->data;
    owns cells(h->data, n);
} by {
    step(); step();
    loop {
        owns h->data;
        owns cells(h->data, n);
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        initialize by close();
        maintain by {
            unfold(cells(h->data, n));
            step(); step(); step();
            fold(cells(h->data, n));
        }
    }
}
```
```expect
fail: loop declares a resource the enclosing function does not hold
```
