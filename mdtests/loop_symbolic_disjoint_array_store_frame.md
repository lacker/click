# A symbolic loop read survives a disjoint store

The loop reads a symbolic `next[cur]` after writing the disjoint `visited`
array. For each guarded index, explicit containment restricts the array
separation to the read cell and the written cell. A `preserve` step carries
that read across the store's footprint. Instantiating the saved bounded-value
invariant and rewriting with the preserved equality restores the invariant
before the next iteration. An unrelated existential fact remains in scope.

```c filename=loop_symbolic_disjoint_array_store_frame.c
void traverse(int32 *next, int32 *visited, int32 n, int32 from, int32 to) {
    int32 cur = from;
    while (visited[cur] == 0) {
        if (cur == to) return;
        visited[cur] = 1;
        cur = next[cur];
    }
}
```

```click
verifying "loop_symbolic_disjoint_array_store_frame.c";

void traverse(int32 *next, int32 *visited, int32 n, int32 from, int32 to) diverges {
    requires 0 <= from;
    requires from < n;
    requires n <= 1073741823;
    views next[0..n];
    owns visited[0..n];
    requires separate(memory(next[0..n]), memory(visited[0..n]));
    requires forall (k: int32) {
        0 <= k and k < n implies 0 <= next[k] and next[k] < n
    };
} by {
    step();
    step();
    have exists (fuel: Nat) { fuel == Nat::Zero } by {
        witness(Nat::Zero);
        close();
    }
    loop diverges {
        invariant 0 <= cur;
        invariant cur < n;
        invariant forall (k: int32) {
            0 <= k and k < n implies 0 <= next[k] and next[k] < n
        };
        views next[0..n];
        owns visited[0..n];
        initialize by { close(); }
        maintain by {
            mark iter;
            have 0 <= next[cur] and next[cur] < n by {
                instantiate(forall (k: int32) {
                    0 <= k and k < n implies 0 <= next[k] and next[k] < n
                }, cur);
                close();
            }
            if cur == to {
                step();
                step();
                close();
            } else {
                step();
            }
            step();
            step();
            have forall (k: int32) {
                0 <= k and k < n implies at(iter, next[k]) == next[k]
            } by {
                intro(); intro();
                have contains(memory(visited[0..n]), memory(visited[cur])) by {
                    apply(click::separation::contains_element(visited, 0, n, cur));
                }
                have contains(memory(next[0..n]), memory(next[k])) by {
                    apply(click::separation::contains_element(next, 0, n, k));
                }
                have separate(memory(visited[cur]), memory(next[k])) by {
                    apply(click::separation::separate_restrict(memory(visited[0..n]), memory(next[0..n]), memory(visited[cur]), memory(next[k])));
                }
                have separate(loop(0).statement(1).footprint, memory(next[k])) by {
                    close() using { separate(memory(visited[cur]), memory(next[k])); };
                }
                have next[k] == at(iter, next[k]) by {
                    preserve(memory(next[k]), loop(0).statement(1));
                }
                close();
            }
            have forall (k: int32) {
                0 <= k and k < n implies 0 <= next[k] and next[k] < n
            } by {
                intro(); intro();
                instantiate(at(iter, forall (j: int32) {
                    0 <= j and j < n implies 0 <= next[j] and next[j] < n
                }), k);
                instantiate(forall (j: int32) {
                    0 <= j and j < n implies at(iter, next[j]) == next[j]
                }, k);
                rewrite(next[k], at(iter, next[k]));
                close();
            }
            have 0 <= next[cur] and next[cur] < n by {
                instantiate(forall (k: int32) {
                    0 <= k and k < n implies 0 <= next[k] and next[k] < n
                }, cur);
                close();
            }
            step();
            have 0 <= cur by { close(); }
            have cur < n by { close(); }
        }
    }
}
```

```expect
pass
```
