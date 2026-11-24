# Indexed reads across a call that writes two regions

The callee writes one cell in each of two separate global arrays. Its
caller states that the readable range containing `a[0]` is separate from
both writes. Expansion proves separation from each footprint member,
then preserves the indexed read across the call.

```c filename=indexed_reads_across_multi_write_calls.c
int32 g[4];
int32 h[4];

void touch(void) {
    g[0] = 1;
    h[0] = 1;
}

void keep_mask(int32 a[], int32 n) {
    touch();
}

void keep_xor(int32 a[], int32 n) {
    touch();
}

void keep_complement(int32 a[], int32 n) {
    touch();
}

void keep_right_shift(int32 a[], int32 n) {
    touch();
}

void keep_narrowed_read(int32 a[], int32 n) {
    touch();
}

void keep_shift_count(int32 a[], int32 n) {
    touch();
}

void keep_quotient(int32 a[], int32 n) {
    touch();
}

void keep_remainder(int32 a[], int32 n) {
    touch();
}

void keep_conditional_read(int32 a[], int32 n) {
    touch();
}

void keep_upper_bound(int32 a[], int32 n) {
    touch();
}
```

```click
verifying "indexed_reads_across_multi_write_calls.c";

void touch() {
    owns g[0..1];
    owns h[0..1];
}

void keep_mask(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (a[0] & 1) == 1;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    requires separate(memory(a[0..n]), memory(h[0..1]));
    owns g[0..1];
    owns h[0..1];
    ensures (a[0] & 1) == 1;
} by {
    step();
    have (a[0] & 1) == 1 by close();
}

void keep_xor(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (a[0] ^ 1) == 3;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    requires separate(memory(a[0..n]), memory(h[0..1]));
    owns g[0..1];
    owns h[0..1];
    ensures (a[0] ^ 1) == 3;
} by {
    step();
    have (a[0] ^ 1) == 3 by close();
}

void keep_complement(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (~a[0]) == 3;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    requires separate(memory(a[0..n]), memory(h[0..1]));
    owns g[0..1];
    owns h[0..1];
    ensures (~a[0]) == 3;
} by {
    step();
    have (~a[0]) == 3 by close();
}

void keep_right_shift(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (a[0] >> 1) == 3;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    requires separate(memory(a[0..n]), memory(h[0..1]));
    owns g[0..1];
    owns h[0..1];
    ensures (a[0] >> 1) == 3;
} by {
    step();
    have (a[0] >> 1) == 3 by close();
}

void keep_narrowed_read(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (a[0] as uint8) == 3;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    requires separate(memory(a[0..n]), memory(h[0..1]));
    owns g[0..1];
    owns h[0..1];
    ensures (a[0] as uint8) == 3;
} by {
    step();
    have (a[0] as uint8) == 3 by close();
}

void keep_shift_count(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (1u32 << (a[0] & 1)) == 2u32;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    requires separate(memory(a[0..n]), memory(h[0..1]));
    owns g[0..1];
    owns h[0..1];
    ensures (1u32 << (a[0] & 1)) == 2u32;
} by {
    step();
    have (1u32 << (a[0] & 1)) == 2u32 by close();
}

void keep_quotient(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires a[0] / 2 == 1;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    requires separate(memory(a[0..n]), memory(h[0..1]));
    owns g[0..1];
    owns h[0..1];
    ensures a[0] / 2 == 1;
} by {
    step();
    have a[0] / 2 == 1 by close();
}

void keep_remainder(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires a[0] % 2 == 1;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    requires separate(memory(a[0..n]), memory(h[0..1]));
    owns g[0..1];
    owns h[0..1];
    ensures a[0] % 2 == 1;
} by {
    step();
    have a[0] % 2 == 1 by close();
}

void keep_conditional_read(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (if n == 1 { a[0] } else { 0 }) == 3;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    requires separate(memory(a[0..n]), memory(h[0..1]));
    owns g[0..1];
    owns h[0..1];
    ensures (if n == 1 { a[0] } else { 0 }) == 3;
} by {
    step();
    have (if n == 1 { a[0] } else { 0 }) == 3 by close();
}

void keep_upper_bound(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires a[0] <= 7;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    requires separate(memory(a[0..n]), memory(h[0..1]));
    owns g[0..1];
    owns h[0..1];
    ensures a[0] <= 7;
} by {
    step();
    have a[0] <= 7 by close();
}
```

```expect
pass
```
