# a quantified fact that is not an equality crosses a separated store

The bound on every `next[k]` holds at `before`, and the store writes the
separated `visited`. Explicit containment and preservation relate the selected
current read to `before`; instantiation supplies its old bounds.

```c filename=quantified_frame_carries_a_bound_fact_to_the_current_state.c
void mark(int32 *next, int32 *visited, int32 n, int32 cur) {
    visited[cur] = 1;
}
```

```click
verifying "quantified_frame_carries_a_bound_fact_to_the_current_state.c";

void mark(int32 *next, int32 *visited, int32 n, int32 cur) {
    requires 0 <= cur;
    requires cur < n;
    views next[0..n];
    owns visited[0..n];
    requires forall (k: int32) { 0 <= k and k < n implies 0 <= next[k] and next[k] < n };
    ensures forall (k: int32) { 0 <= k and k < n implies 0 <= next[k] and next[k] < n };
} by {
    mark before;
    have at(before, forall (k: int32) { 0 <= k and k < n implies 0 <= next[k] and next[k] < n }) by close();
    have contains(memory(visited[0..n]), memory(visited[cur])) by {
        apply(click::separation::contains_element(visited, 0, n, cur));
    }
    have contains(memory(next[0..n]), memory(next[0..n])) by {
        apply(click::separation::contains_refl(memory(next[0..n])));
    }
    have separate(memory(visited[cur]), memory(next[0..n])) by {
        apply(click::separation::separate_restrict(memory(visited[0..n]), memory(next[0..n]), memory(visited[cur]), memory(next[0..n])));
    }
    step();
    have forall (k: int32) { 0 <= k and k < n implies 0 <= next[k] and next[k] < n } by {
        intro();
        intro();
        have contains(memory(next[0..n]), memory(next[k])) by {
            apply(click::separation::contains_element(next, 0, n, k));
        }
        have contains(memory(visited[cur]), memory(visited[cur])) by {
            apply(click::separation::contains_refl(memory(visited[cur])));
        }
        have separate(memory(visited[cur]), memory(next[k])) by {
            apply(click::separation::separate_restrict(memory(visited[cur]), memory(next[0..n]), memory(visited[cur]), memory(next[k])));
        }
        have separate(statement(0).footprint, memory(next[k])) by {
            close() using { separate(memory(visited[cur]), memory(next[k])); };
        }
        have next[k] == at(before, next[k]) by {
            preserve(memory(next[k]), statement(0));
        }
        instantiate(at(before, forall (j: int32) { 0 <= j and j < n implies 0 <= next[j] and next[j] < n }), k);
        rewrite(next[k], at(before, next[k]));
        close();
    }
}
```

```expect
pass
```
