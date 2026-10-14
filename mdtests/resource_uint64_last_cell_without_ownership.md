# A captured pointer keeps its scalar element type but grants no byte authority

The viewed resource retains the pointer and index types. Neither its view nor
the prefix-validity guarantee grants permission to write the selected cell.

```c filename=probe.c
int32 probe(int32* p, uint64 n, int32 input) {
    p[n - 1] = input;
    return input;
}
```
```click
verifying "probe.c";
resource cell(p: int32*, n: uint64) {
    views p[n - 1u64];
}
int32 probe(int32* p, uint64 n, int32 input) {
    views cell(p, n);
    requires 1u64 <= n;
    requires n <= 2305843009213693951u64;
    requires valid_place(p[0..n]);
    ensures result == input;
} by { unfold(cell(p, n)); execute(); fold(cell(p, n)); simp(); }
```

```expect
fail: missing resource
```
