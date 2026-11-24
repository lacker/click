# A viewed array's cells retain their values across a disjoint store

The universally quantified index selects one cell. Explicit containment
restricts the separated range, then preservation relates its two states.

```c filename=quantified_disjoint_array_store_frame.c
void mark(int32 *next, int32 *visited, int32 n, int32 j) {
    visited[j] = 1;
}
```

```click
verifying "quantified_disjoint_array_store_frame.c";

void mark(int32 *next, int32 *visited, int32 n, int32 j) {
    requires 0 <= n;
    requires n <= 1073741823;
    requires 0 <= j;
    requires j < n;
    views next[0..n];
    owns visited[0..n];
    requires separate(memory(next[0..n]), memory(visited[0..n]));
    requires forall (k: int32) { 0 <= k and k < n implies 0 <= next[k] };
    ensures forall (k: int32) {
        0 <= k and k < n implies at(entry, next[k]) == next[k]
    };
} by {
    mark entry;
    have contains(memory(visited[0..n]), memory(visited[j])) by {
        apply(click::separation::contains_element(visited, 0, n, j));
    }
    have contains(memory(next[0..n]), memory(next[0..n])) by {
        apply(click::separation::contains_refl(memory(next[0..n])));
    }
    have separate(memory(visited[j]), memory(next[0..n])) by {
        apply(click::separation::separate_restrict(memory(visited[0..n]), memory(next[0..n]), memory(visited[j]), memory(next[0..n])));
    }
    step();
    have forall (k: int32) {
        0 <= k and k < n implies at(entry, next[k]) == next[k]
    } by {
        intro();
        intro();
        have contains(memory(next[0..n]), memory(next[k])) by {
            apply(click::separation::contains_element(next, 0, n, k));
        }
        have contains(memory(visited[j]), memory(visited[j])) by {
            apply(click::separation::contains_refl(memory(visited[j])));
        }
        have separate(memory(visited[j]), memory(next[k])) by {
            apply(click::separation::separate_restrict(memory(visited[j]), memory(next[0..n]), memory(visited[j]), memory(next[k])));
        }
        have separate(statement(0).footprint, memory(next[k])) by {
            close() using { separate(memory(visited[j]), memory(next[k])); };
        }
        have next[k] == at(entry, next[k]) by {
            preserve(memory(next[k]), statement(0));
        }
        close();
    }
}
```

```expect
pass
```
