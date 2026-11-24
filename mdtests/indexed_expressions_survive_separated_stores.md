# Indexed expressions survive separated stores

The global store leaves `a[0]` unchanged, including in a bitwise expression
or an upper bound. The symbolic store leaves `p[j]` unchanged in an `if`
condition written with the indexed read on either side. The stated separation
covers the containing range. Expansion restricts that separation to the
indexed cell and uses `preserve` to justify the read across the store.

```c filename=indexed_expressions_survive_separated_stores.c
int32 g[4];

void keep_low_bit(int32 a[], int32 n) {
    g[0] = 1;
}

void keep_positive_flag(int32 p[], int32 i, int32 j, int32 n) {
    p[i] = 9;
}

void keep_bitwise_or(int32 a[], int32 n) {
    g[0] = 1;
}

void keep_read_bound(int32 a[], int32 n) {
    g[0] = 1;
}

void keep_reversed_condition(int32 p[], int32 i, int32 j, int32 n) {
    p[i] = 9;
}
```

```click
verifying "indexed_expressions_survive_separated_stores.c";
import click::separation;

void keep_low_bit(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (a[0] & 1) == 1;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures (a[0] & 1) == 1;
    ensures g[0] == 1;
} by {
    step();
    have (a[0] & 1) == 1 by close();
}

void keep_positive_flag(int32 p[], int32 i, int32 j, int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    requires i >= 0;
    requires i < n;
    requires j >= 0;
    requires j < n;
    consumes p[i..i + 1];
    views p[j..j + 1];
    requires separate(memory(p[i..i + 1]), memory(p[j..j + 1]));
    requires (if p[j] > 0 { 1 } else { 0 }) == 1;
    ensures (if p[j] > 0 { 1 } else { 0 }) == 1;
} by {
    have contains(memory(p[i..i + 1]), memory((p + i)[0..1])) by { normalize(); }
    have contains(memory(p[j..j + 1]), memory(p[j..j + 1])) by {
        apply(separation::contains_refl(memory(p[j..j + 1])));
    }
    have separate(memory((p + i)[0..1]), memory(p[j..j + 1])) by {
        apply(separation::separate_restrict(memory(p[i..i + 1]), memory(p[j..j + 1]), memory((p + i)[0..1]), memory(p[j..j + 1])));
    }
    step() by { close(); }
    have (if p[j] > 0 { 1 } else { 0 }) == 1 by close();
}

void keep_bitwise_or(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (a[0] | 1) == 3;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures (a[0] | 1) == 3;
    ensures g[0] == 1;
} by {
    step();
    have (a[0] | 1) == 3 by close();
}

void keep_read_bound(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires a[0] <= 7;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures a[0] <= 7;
    ensures g[0] == 1;
} by {
    step();
    have a[0] <= 7 by close();
}

void keep_reversed_condition(int32 p[], int32 i, int32 j, int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    requires i >= 0;
    requires i < n;
    requires j >= 0;
    requires j < n;
    consumes p[i..i + 1];
    views p[j..j + 1];
    requires separate(memory(p[i..i + 1]), memory(p[j..j + 1]));
    requires (if 0 < p[j] { 1 } else { 0 }) == 1;
    ensures (if 0 < p[j] { 1 } else { 0 }) == 1;
} by {
    have contains(memory(p[i..i + 1]), memory((p + i)[0..1])) by { normalize(); }
    have contains(memory(p[j..j + 1]), memory(p[j..j + 1])) by {
        apply(separation::contains_refl(memory(p[j..j + 1])));
    }
    have separate(memory((p + i)[0..1]), memory(p[j..j + 1])) by {
        apply(separation::separate_restrict(memory(p[i..i + 1]), memory(p[j..j + 1]), memory((p + i)[0..1]), memory(p[j..j + 1])));
    }
    step() by { close(); }
    have (if 0 < p[j] { 1 } else { 0 }) == 1 by close();
}
```

```expect
pass
```
