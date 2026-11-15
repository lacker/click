# A viewed array's cells retain their values across a disjoint store

The index is universally quantified, so load naming must keep both states
on the store's recorded history rather than rely on one concrete cell.

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
        apply(click::separation::contains_element(visited, 0, n, j)) using { 0 <= j; j < n; };
    }
    have contains(memory(next[0..n]), memory(next[0..n])) by {
        apply(click::separation::contains_refl(memory(next[0..n])));
    }
    have separate(memory(visited[j]), memory(next[0..n])) by {
        apply(click::separation::separate_restrict(memory(visited[0..n]), memory(next[0..n]), memory(visited[j]), memory(next[0..n]))) using {
            separate(memory(visited[0..n]), memory(next[0..n]));
            contains(memory(visited[0..n]), memory(visited[j]));
            contains(memory(next[0..n]), memory(next[0..n]));
        };
    }
    step();
    have forall (k: int32) {
        0 <= k and k < n implies at(entry, next[k]) == next[k]
    } by {
        intro();
        intro();
        have at(entry, next[k]) == at(entry, next[k]) by normalize();
        transport(
            at(entry, next[k]) == at(entry, next[k]),
            at(entry, next[k]) == next[k]
        ) using {
            at(entry, next[k]) == at(entry, next[k]);
            0 <= k;
            k < n;
            separate(memory(next[0..n]), memory(visited[0..n]));
        };
        solve();
    }
}
```

```expect
pass
```
