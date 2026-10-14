# A captured pointer keeps its scalar element type

Instantiating `cell(p, n)` substitutes complete pointer and integer values into
the indexed address. The last-cell ownership remains separate from the prefix
geometry; the preceding cells are neither owned nor initialized.

```c filename=probe.c
int32 probe(int32* p, uint64 n, int32 input) {
    p[n - 1] = input;
    return input;
}
```
```click
verifying "probe.c";
resource cell(p: int32*, n: uint64) {
    owns p[n - 1u64];
}
int32 probe(int32* p, uint64 n, int32 input) {
    owns cell(p, n);
    requires 1u64 <= n;
    requires n <= 2305843009213693951u64;
    requires valid_place(p[0..n]);
    ensures result == input;
} by { unfold(cell(p, n)); execute(); fold(cell(p, n)); simp(); }
```

```expect
pass
```
