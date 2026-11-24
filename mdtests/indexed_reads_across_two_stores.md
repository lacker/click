# Indexed reads across two separate stores

Both global stores are disjoint from the indexed read `a[0]`. Each proof
uses `solve` for a fact that was true before either store. Expansion
preserves the read across each store and composes the endpoint equalities
to rewrite the original fact.

```c filename=indexed_reads_across_two_stores.c
int32 g[4];

void keep_mask(int32 a[], int32 n) {
    g[0] = 1;
    g[1] = 1;
}

void keep_xor(int32 a[], int32 n) {
    g[0] = 1;
    g[1] = 1;
}

void keep_complement(int32 a[], int32 n) {
    g[0] = 1;
    g[1] = 1;
}

void keep_right_shift(int32 a[], int32 n) {
    g[0] = 1;
    g[1] = 1;
}

void keep_narrowed_read(int32 a[], int32 n) {
    g[0] = 1;
    g[1] = 1;
}

void keep_shift_count(int32 a[], int32 n) {
    g[0] = 1;
    g[1] = 1;
}

void keep_quotient(int32 a[], int32 n) {
    g[0] = 1;
    g[1] = 1;
}

void keep_remainder(int32 a[], int32 n) {
    g[0] = 1;
    g[1] = 1;
}

void keep_conditional_read(int32 a[], int32 n) {
    g[0] = 1;
    g[1] = 1;
}

void keep_upper_bound(int32 a[], int32 n) {
    g[0] = 1;
    g[1] = 1;
}
```

```click
verifying "indexed_reads_across_two_stores.c";

void keep_mask(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (a[0] & 1) == 1;
    requires separate(memory(a[0..n]), memory(g[0..2]));
    owns g[0..2];
    ensures (a[0] & 1) == 1;
} by {
    step();
    step();
    have (a[0] & 1) == 1 by close();
}

void keep_xor(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (a[0] ^ 1) == 3;
    requires separate(memory(a[0..n]), memory(g[0..2]));
    owns g[0..2];
    ensures (a[0] ^ 1) == 3;
} by {
    step();
    step();
    have (a[0] ^ 1) == 3 by close();
}

void keep_complement(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (~a[0]) == 3;
    requires separate(memory(a[0..n]), memory(g[0..2]));
    owns g[0..2];
    ensures (~a[0]) == 3;
} by {
    step();
    step();
    have (~a[0]) == 3 by close();
}

void keep_right_shift(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (a[0] >> 1) == 3;
    requires separate(memory(a[0..n]), memory(g[0..2]));
    owns g[0..2];
    ensures (a[0] >> 1) == 3;
} by {
    step();
    step();
    have (a[0] >> 1) == 3 by close();
}

void keep_narrowed_read(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (a[0] as uint8) == 3;
    requires separate(memory(a[0..n]), memory(g[0..2]));
    owns g[0..2];
    ensures (a[0] as uint8) == 3;
} by {
    step();
    step();
    have (a[0] as uint8) == 3 by close();
}

void keep_shift_count(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (1u32 << (a[0] & 1)) == 2u32;
    requires separate(memory(a[0..n]), memory(g[0..2]));
    owns g[0..2];
    ensures (1u32 << (a[0] & 1)) == 2u32;
} by {
    step();
    step();
    have (1u32 << (a[0] & 1)) == 2u32 by close();
}

void keep_quotient(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires a[0] / 2 == 1;
    requires separate(memory(a[0..n]), memory(g[0..2]));
    owns g[0..2];
    ensures a[0] / 2 == 1;
} by {
    step();
    step();
    have a[0] / 2 == 1 by close();
}

void keep_remainder(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires a[0] % 2 == 1;
    requires separate(memory(a[0..n]), memory(g[0..2]));
    owns g[0..2];
    ensures a[0] % 2 == 1;
} by {
    step();
    step();
    have a[0] % 2 == 1 by close();
}

void keep_conditional_read(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (if n == 1 { a[0] } else { 0 }) == 3;
    requires separate(memory(a[0..n]), memory(g[0..2]));
    owns g[0..2];
    ensures (if n == 1 { a[0] } else { 0 }) == 3;
} by {
    step();
    step();
    have (if n == 1 { a[0] } else { 0 }) == 3 by close();
}

void keep_upper_bound(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires a[0] <= 7;
    requires separate(memory(a[0..n]), memory(g[0..2]));
    owns g[0..2];
    ensures a[0] <= 7;
} by {
    step();
    step();
    have a[0] <= 7 by close();
}
```

```expect
pass
```
