# a quantified fact crosses a store its guard excludes

`k != i` excludes the one cell `v[i] = 1` writes, so every other entry
value survives the store. Introduce the index, apply `separate_elements`,
and preserve that selected cell across the statement footprint.

```c filename=quantified_frame_carries_a_fact_past_the_excluded_store.c
void mark(int32 *v, int32 n, int32 i) {
    v[i] = 1;
}
```

```click
verifying "quantified_frame_carries_a_fact_past_the_excluded_store.c";

void mark(int32 *v, int32 n, int32 i) {
    requires 0 <= i;
    requires i < n;
    owns v[0..n];
    ensures forall (k: int32) { 0 <= k and k < n and k != i implies v[k] == old(v[k]) };
} by {
    step();
    have forall (k: int32) { 0 <= k and k < n and k != i implies v[k] == old(v[k]) } by {
        intro();
        intro();
        have k != i by close();
        have separate(memory(v[i]), memory(v[k])) by {
            apply(click::separation::separate_elements(v, i, k));
        }
        have separate(statement(0).footprint, memory(v[k])) by {
            close() using { separate(memory(v[i]), memory(v[k])); };
        }
        preserve(memory(v[k]), statement(0));
    }
}
```

```expect
pass
```
