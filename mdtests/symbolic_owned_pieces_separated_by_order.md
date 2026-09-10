# Ordered indexes let a caller supply two owned pieces of one range

Same callee as `symbolic_owned_pieces_caller_must_prove_separation.md`. The
caller now requires `i < j`, so `p[j..j + 1]` is carved from the residue above
`p[i..i + 1]` and both pieces are handed over. The callee's `p[i] == 1`, which
relies on the two cells being distinct, comes back to the caller.

```c filename=symbolic_owned_pieces_separated_by_order.c
void write_pieces(int32 p[], int32 n, int32 i, int32 j) {
    p[i] = 1;
    p[j] = 2;
}

void call_pieces(int32 p[], int32 n, int32 i, int32 j) {
    write_pieces(p, n, i, j);
}
```

```click
verifying "symbolic_owned_pieces_separated_by_order.c";

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
    requires i < j;
    owns p[0..n];
    ensures p[i] == 1;
} by auto;
```

```expect
pass
```
