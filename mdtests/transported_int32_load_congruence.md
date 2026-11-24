# Checked transport composes with same-state load congruence

The store writes `p[k]`. The element-separation law uses `i != k` to prove that
the store misses `p[i]`, and `preserve` checks that the read keeps its entry
value. The next `have` rewrites the current index from `j` to `i` using
`i == j`, then closes with the saved read equality. The implicit proof tail
closes the postcondition and returns ownership of the array.

```c filename=transported_int32_loads.c
void write_other(int32 p[], int32 n, int32 i, int32 j, int32 k) {
    p[k] = 9;
}
```

```click
verifying "transported_int32_loads.c";

void write_other(int32 p[], int32 n, int32 i, int32 j, int32 k) {
    owns p[0..n];
    requires 0 <= i;
    requires i < n;
    requires 0 <= j;
    requires j < n;
    requires 0 <= k;
    requires k < n;
    requires i == j;
    requires i != k;
    ensures p[j] == old(p[i]);
} by {
    mark entry;
    step();
    have p[i] == at(entry, p[i]) by {
        have separate(memory(p[k]), memory(p[i])) by {
            apply(click::separation::separate_elements(p, k, i));
        }
        have separate(statement(0).footprint, memory(p[i])) by {
            close() using { separate(memory(p[k]), memory(p[i])); };
        }
        preserve(memory(p[i]), statement(0));
    }
    have p[j] == at(entry, p[i]) by {
        rewrite(j, i);
        close();
    }
}
```

```expect
pass
```
