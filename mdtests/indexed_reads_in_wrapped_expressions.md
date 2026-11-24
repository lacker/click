# Indexed reads inside shifts, casts, and other expressions

The contract separates a global store from the indexed read `a[0]`.
Each proof leaves a comparison involving that read to `solve`. Expansion
identifies the read, preserves it across the store, and rewrites the
comparison using the preserved equality.

```c filename=indexed_reads_in_wrapped_expressions.c
int32 g[4];

void keep_masked_left_shift(int32 a[], int32 n) {
    g[0] = 1;
}

void keep_left_shift_count(int32 a[], int32 n) {
    g[0] = 1;
}

void keep_right_shift_count(int32 a[], int32 n) {
    g[0] = 1;
}

void keep_narrowed_read(int32 a[], int32 n) {
    g[0] = 1;
}

void keep_unsigned_shift(int32 a[], int32 n) {
    g[0] = 1;
}

void keep_quotient(int32 a[], int32 n) {
    g[0] = 1;
}

void keep_remainder(int32 a[], int32 n) {
    g[0] = 1;
}

void keep_read_in_conditional_arm(int32 a[], int32 n) {
    g[0] = 1;
}
```

```click
verifying "indexed_reads_in_wrapped_expressions.c";

void keep_masked_left_shift(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (((a[0] & 3) << 1) & 7) == 4;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures (((a[0] & 3) << 1) & 7) == 4;
    ensures g[0] == 1;
} by {
    step();
    have (((a[0] & 3) << 1) & 7) == 4 by close();
}

void keep_left_shift_count(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (1u32 << (a[0] & 1)) == 2u32;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures (1u32 << (a[0] & 1)) == 2u32;
    ensures g[0] == 1;
} by {
    step();
    have (1u32 << (a[0] & 1)) == 2u32 by close();
}

void keep_right_shift_count(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (8 >> (a[0] & 1)) == 4;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures (8 >> (a[0] & 1)) == 4;
    ensures g[0] == 1;
} by {
    step();
    have (8 >> (a[0] & 1)) == 4 by close();
}

void keep_narrowed_read(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (a[0] as uint8) == 3;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures (a[0] as uint8) == 3;
    ensures g[0] == 1;
} by {
    step();
    have (a[0] as uint8) == 3 by close();
}

void keep_unsigned_shift(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires ((a[0] as uint32) >> 2) == 3u32;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures ((a[0] as uint32) >> 2) == 3u32;
    ensures g[0] == 1;
} by {
    step();
    have ((a[0] as uint32) >> 2) == 3u32 by close();
}

void keep_quotient(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires a[0] / 2 == 1;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures a[0] / 2 == 1;
    ensures g[0] == 1;
} by {
    step();
    have a[0] / 2 == 1 by close();
}

void keep_remainder(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires a[0] % 2 == 1;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures a[0] % 2 == 1;
    ensures g[0] == 1;
} by {
    step();
    have a[0] % 2 == 1 by close();
}

void keep_read_in_conditional_arm(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (if n == 1 { a[0] } else { 0 }) == 3;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures (if n == 1 { a[0] } else { 0 }) == 3;
    ensures g[0] == 1;
} by {
    step();
    have (if n == 1 { a[0] } else { 0 }) == 3 by close();
}
```

```expect
pass
```
