# Guarded definedness does not survive free

A typed-read fact at entry cannot establish a valid read after deallocation.

```c filename=dispose.c
void dispose(int32 *data, int32 n) { free(data); }
```

```click
verifying "dispose.c";
resource cell(p: int32*, n: int32) {
    owns allocation(p, n * 4);
    owns p[0..n];
}
void dispose(int32 *data, int32 n) {
    requires 0 < n;
    requires n < 100;
    consumes cell(data, n);
    requires forall (k: int32) { 0 <= k and k < n implies defined(data[k]) };
    ensures forall (k: int32) { 0 <= k and k < n implies defined(data[k]) };
} by {
    unfold(cell(data, n));
    step();
    have forall (k: int32) { 0 <= k and k < n implies defined(data[k]) } by { close(); }
}
```

```expect
fail: `solve` failed
```
