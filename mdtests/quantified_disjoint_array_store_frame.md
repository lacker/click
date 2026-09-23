# A viewed array's cells retain their values across a disjoint store

The index is universally quantified, so load naming must keep both snapshots
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
    consumes visited[0..n];
    produces visited[0..n];
    requires separate(memory(next[0..n]), memory(visited[0..n]));
    requires forall (k: int32) { 0 <= k and k < n implies 0 <= next[k] };
    ensures forall (k: int32) {
        0 <= k and k < n implies at(entry, next[k]) == next[k]
    };
} by {
    mark entry;
    step();
    have forall (k: int32) {
        0 <= k and k < n implies at(entry, next[k]) == next[k]
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < n);
        have at(entry, next[k]) == at(entry, next[k]) by { normalize(); }
        transport(
            at(entry, next[k]) == at(entry, next[k]),
            at(entry, next[k]) == next[k]
        ) using {
            at(entry, next[k]) == at(entry, next[k]);
            0 <= k;
            k < n;
            separate(memory(next[0..n]), memory(visited[0..n]));
        }
        simp();
    }
    execute();
    simp();
}
```

```expect
pass
```
