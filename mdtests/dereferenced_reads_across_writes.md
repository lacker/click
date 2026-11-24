# Pointer dereferences across separated writes

Each caller proves a comparison involving `*a` or `*(a + 1)` after a
single store, successive stores, or a call that writes two regions.
Expansion names the dereferenced cell and preserves it across each
recorded footprint used by the proof.

```c filename=dereferenced_reads_across_writes.c
int32 g[4];
int32 h[4];

void touch(void) {
    g[0] = 1;
    h[0] = 1;
}

void keep_pointer_xor(int32 a[], int32 n) {
    g[0] = 1;
}

void keep_pointer_complement(int32 a[], int32 n) {
    g[0] = 1;
}

void keep_pointer_byte(int32 a[], int32 n) {
    g[0] = 1;
}

void keep_pointer_shift_count(int32 a[], int32 n) {
    g[0] = 1;
}

void keep_offset_byte_across_stores(int32 a[], int32 n) {
    g[0] = 1;
    g[1] = 1;
}

void keep_pointer_shift_across_stores(int32 a[], int32 n) {
    g[0] = 1;
    g[1] = 1;
}

void keep_pointer_choice_across_stores(int32 a[], int32 n) {
    g[0] = 1;
    g[1] = 1;
}

void keep_pointer_quotient_across_call(int32 a[], int32 n) {
    touch();
}

void keep_offset_remainder_across_call(int32 a[], int32 n) {
    touch();
}

void keep_pointer_mask_across_call(int32 a[], int32 n) {
    touch();
}
```

```click
verifying "dereferenced_reads_across_writes.c";

void touch() {
    owns g[0..1];
    owns h[0..1];
}

void keep_pointer_xor(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (*a ^ 1) == 3;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures (*a ^ 1) == 3;
    ensures g[0] == 1;
} by {
    step();
    have (*a ^ 1) == 3 by close();
}

void keep_pointer_complement(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (~*a) == 3;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures (~*a) == 3;
    ensures g[0] == 1;
} by {
    step();
    have (~*a) == 3 by close();
}

void keep_pointer_byte(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (*a as uint8) == 3;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures (*a as uint8) == 3;
    ensures g[0] == 1;
} by {
    step();
    have (*a as uint8) == 3 by close();
}

void keep_pointer_shift_count(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (1u32 << (*a & 1)) == 2u32;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures (1u32 << (*a & 1)) == 2u32;
    ensures g[0] == 1;
} by {
    step();
    have (1u32 << (*a & 1)) == 2u32 by close();
}

void keep_offset_byte_across_stores(int32 a[], int32 n) {
    requires 1 < n;
    requires viewable(a[0..n]);
    requires (*(a + 1) as uint8) == 3;
    requires separate(memory(a[0..n]), memory(g[0..2]));
    owns g[0..2];
    ensures (*(a + 1) as uint8) == 3;
} by {
    step();
    step();
    have (*(a + 1) as uint8) == 3 by close();
}

void keep_pointer_shift_across_stores(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (*a >> 1) == 3;
    requires separate(memory(a[0..n]), memory(g[0..2]));
    owns g[0..2];
    ensures (*a >> 1) == 3;
} by {
    step();
    step();
    have (*a >> 1) == 3 by close();
}

void keep_pointer_choice_across_stores(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (if n == 1 { *a } else { 0 }) == 3;
    requires separate(memory(a[0..n]), memory(g[0..2]));
    owns g[0..2];
    ensures (if n == 1 { *a } else { 0 }) == 3;
} by {
    step();
    step();
    have (if n == 1 { *a } else { 0 }) == 3 by close();
}

void keep_pointer_quotient_across_call(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires *a / 2 == 1;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    requires separate(memory(a[0..n]), memory(h[0..1]));
    owns g[0..1];
    owns h[0..1];
    ensures *a / 2 == 1;
} by {
    step();
    have *a / 2 == 1 by close();
}

void keep_offset_remainder_across_call(int32 a[], int32 n) {
    requires 1 < n;
    requires viewable(a[0..n]);
    requires *(a + 1) % 2 == 1;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    requires separate(memory(a[0..n]), memory(h[0..1]));
    owns g[0..1];
    owns h[0..1];
    ensures *(a + 1) % 2 == 1;
} by {
    step();
    have *(a + 1) % 2 == 1 by close();
}

void keep_pointer_mask_across_call(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (*a & 1) == 1;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    requires separate(memory(a[0..n]), memory(h[0..1]));
    owns g[0..1];
    owns h[0..1];
    ensures (*a & 1) == 1;
} by {
    step();
    have (*a & 1) == 1 by close();
}
```

```expect
pass
```
