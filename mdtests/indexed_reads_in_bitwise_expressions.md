# Indexed reads in bitwise expressions

A write to `g[0]` leaves the separated read of `a[0]` unchanged. Each
proof leaves the bitwise comparison to `solve`. Expansion identifies the
indexed read through the bitwise operators and preserves it across the store.

```c filename=indexed_reads_in_bitwise_expressions.c
int32 g[4];

void keep_xor(int32 a[], int32 n) {
    g[0] = 1;
}

void keep_complement(int32 a[], int32 n) {
    g[0] = 1;
}

void keep_right_shift(int32 a[], int32 n) {
    g[0] = 1;
}

void keep_literal_first_mask(int32 a[], int32 n) {
    g[0] = 1;
}

void keep_nested_masks(int32 a[], int32 n) {
    g[0] = 1;
}
```

```click
verifying "indexed_reads_in_bitwise_expressions.c";

void keep_xor(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (a[0] ^ 1) == 3;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures (a[0] ^ 1) == 3;
    ensures g[0] == 1;
} by {
    step();
    have (a[0] ^ 1) == 3 by close();
}

void keep_complement(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (~a[0]) == 3;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures (~a[0]) == 3;
    ensures g[0] == 1;
} by {
    step();
    have (~a[0]) == 3 by close();
}

void keep_right_shift(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (a[0] >> 1) == 3;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures (a[0] >> 1) == 3;
    ensures g[0] == 1;
} by {
    step();
    have (a[0] >> 1) == 3 by close();
}

void keep_literal_first_mask(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (1 & a[0]) == 1;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures (1 & a[0]) == 1;
    ensures g[0] == 1;
} by {
    step();
    have (1 & a[0]) == 1 by close();
}

void keep_nested_masks(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires ((a[0] & 3) | 4) == 5;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures ((a[0] & 3) | 4) == 5;
    ensures g[0] == 1;
} by {
    step();
    have ((a[0] & 3) | 4) == 5 by close();
}
```

```expect
pass
```
