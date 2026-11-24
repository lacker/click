# a separated array is not framed across its own release

`data` is consumed and released by `free`. Separation from the rest of the
contract says nothing about liveness, and the released cells are not framed
back to their entry values.

```c filename=quantified_frame_rejects_a_freed_array.c
void dispose(int32 *data, int32 n) { free(data); }
```

```click
verifying "quantified_frame_rejects_a_freed_array.c";

resource cell(p: int32*, n: int32) {
    owns allocation(p, n * 4);
    owns p[0..n];
}

void dispose(int32 *data, int32 n) {
    requires 0 < n;
    requires n < 100;
    consumes cell(data, n);
    ensures forall (k: int32) { 0 <= k and k < n implies data[k] == old(data[k]) };
} by {
    unfold(cell(data, n));
    step();
    have forall (k: int32) { 0 <= k and k < n implies data[k] == old(data[k]) } by { close(); }
}
```

```expect
fail: `solve` failed
```
