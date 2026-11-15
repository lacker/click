# Checked transport composes with same-state load congruence

The store writes `p[k]`. The element-separation law uses `i != k` to establish that
the store misses `p[i]`; `preserve` retains its entry value. The next `have` uses only the trusted equality
graph: `i == j` identifies the current reads, and the transported equality
connects that value to the entry state. The final `solve` closes the
postcondition and returns ownership of the array.

The graph does not infer that the store is disjoint, and equality of this one
read does not make the states interchangeable.

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
            apply(click::separation::separate_elements(p, k, i)) using { i != k; };
        }
        have separate(statement(0).footprint, memory(p[i])) by {
            normalize() using { separate(memory(p[k]), memory(p[i])); };
        }
        preserve(separate(statement(0).footprint, memory(p[i])));
    }
    have p[j] == at(entry, p[i]) by {
        normalize() using { };
    }
}
```

```expect
pass
```
