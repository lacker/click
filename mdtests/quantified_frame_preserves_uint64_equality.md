# A quantified uint64 equality crosses a separated store

The proof selects a bounded element, restricts the separated resource range,
and preserves the complete 64-bit read across the store. Instantiating the
entry-state fact then establishes its current value.

```c filename=probe.c
void mark(unsigned long *values, int32 *visited, int32 n, int32 cur, unsigned long stamp) {
    visited[cur] = 1;
}
```

```click
verifying "probe.c";
void mark(uint64 *values, int32 *visited, int32 n, int32 cur, uint64 stamp) {
    requires 0 <= cur;
    requires cur < n;
    views values[0..n];
    owns visited[0..n];
    requires forall (k: int32) { 0 <= k and k < n implies values[k] == stamp };
    ensures forall (k: int32) { 0 <= k and k < n implies values[k] == stamp };
} by {
    mark before;
    have at(before, forall (k: int32) { 0 <= k and k < n implies values[k] == stamp }) by close();
    have contains(memory(visited[0..n]), memory(visited[cur])) by {
        apply(click::separation::contains_element(visited, 0, n, cur));
    }
    have contains(memory(values[0..n]), memory(values[0..n])) by {
        apply(click::separation::contains_refl(memory(values[0..n])));
    }
    have separate(memory(visited[cur]), memory(values[0..n])) by {
        apply(click::separation::separate_restrict(memory(visited[0..n]), memory(values[0..n]), memory(visited[cur]), memory(values[0..n])));
    }
    step();
    have forall (k: int32) { 0 <= k and k < n implies values[k] == stamp } by {
        intro();
        intro();
        have contains(memory(values[0..n]), memory(values[k])) by {
            apply(click::separation::contains_element(values, 0, n, k));
        }
        have contains(memory(visited[cur]), memory(visited[cur])) by {
            apply(click::separation::contains_refl(memory(visited[cur])));
        }
        have separate(memory(visited[cur]), memory(values[k])) by {
            apply(click::separation::separate_restrict(memory(visited[cur]), memory(values[0..n]), memory(visited[cur]), memory(values[k])));
        }
        have separate(statement(0).footprint, memory(values[k])) by {
            close() using { separate(memory(visited[cur]), memory(values[k])); };
        }
        have values[k] == at(before, values[k]) by {
            preserve(memory(values[k]), statement(0));
        }
        instantiate(at(before, forall (j: int32) { 0 <= j and j < n implies values[j] == stamp }), k);
        rewrite(values[k], at(before, values[k]));
        close();
    }
}
```

```expect
pass
```
