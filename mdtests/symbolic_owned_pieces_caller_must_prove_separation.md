# A caller cannot hand out two symbolic owned pieces it cannot separate

The callee declares `owns p[i..i + 1]` and `owns p[j..j + 1]` beside a view of
the whole range. Declared owned resources are separate by composition, so the
callee's proof may treat the two cells as distinct. That separation is a debt
the caller pays: carving `p[j..j + 1]` out of what remains of `p[0..n]` after
`p[i..i + 1]` is taken needs `j` placed on one side of `i`. With no premise
relating `i` and `j`, the second piece cannot be supplied and the call fails.

```c filename=symbolic_owned_pieces_caller_must_prove_separation.c
void write_pieces(int32 p[], int32 n, int32 i, int32 j) {
    p[i] = 1;
    p[j] = 2;
}

void call_pieces(int32 p[], int32 n, int32 i, int32 j) {
    write_pieces(p, n, i, j);
}
```

```click
verifying "symbolic_owned_pieces_caller_must_prove_separation.c";

void write_pieces(int32 p[], int32 n, int32 i, int32 j) {
    requires n >= 0;
    requires i >= 0;
    requires i < n;
    requires j >= 0;
    requires j < n;
    requires loadable(p[0..n]);
    views p[0..n];
    owns p[i..i + 1];
    owns p[j..j + 1];
    ensures p[i] == 1;
} by auto;

void call_pieces(int32 p[], int32 n, int32 i, int32 j) {
    requires n >= 0;
    requires i >= 0;
    requires i < n;
    requires j >= 0;
    requires j < n;
    requires loadable(p[0..n]);
    owns p[0..n];
    ensures p[i] == 1;
} by auto;
```

```expect
fail: missing resource fact
```
