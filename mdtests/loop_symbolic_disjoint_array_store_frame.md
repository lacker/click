# A symbolic array load remains on the loop store's history

The loop reads a symbolic `next[cur]` after writing the disjoint `visited`
array. One quantified transport carries every guarded `next[k]` value from
the iteration-entry snapshot through the store, inside a `have` in `preserve`.
The guard supplies the read index bounds, and the `using` list supplies the
write index bounds and separation. An unrelated existential fact keeps the
proof on the explicit transport path.

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
        witness(fuel = Nat::Zero);
        normalize();
    }
    loop diverges {
        invariant 0 <= cur;
        invariant cur < n;
        invariant forall (k: int32) {
            0 <= k and k < n implies 0 <= next[k] and next[k] < n
        };
        views next[0..n];
        owns visited[0..n];
        initialize by { simp(); }
        preserve by {
            mark iter;
            have forall (k: int32) {
                0 <= k and k < n implies at(iter, next[k]) == at(iter, next[k])
            } by {
                intro(); intro(); normalize();
            }
            have 0 <= next[cur] and next[cur] < n by {
                instantiate(forall (k: int32) {
                    0 <= k and k < n implies 0 <= next[k] and next[k] < n
                }, cur) using { 0 <= cur; cur < n; }
                assumption();
            }
            if cur == to {
                step();
                step();
                simp();
            } else {
                step();
            }
            step();
            step();
            have forall (k: int32) {
                0 <= k and k < n implies at(iter, next[k]) == next[k]
            } by {
                transport(
                    forall (k: int32) {
                        0 <= k and k < n implies at(iter, next[k]) == at(iter, next[k])
                    },
                    forall (k: int32) {
                        0 <= k and k < n implies at(iter, next[k]) == next[k]
                    }
                ) using {
                    forall (k: int32) {
                        0 <= k and k < n implies at(iter, next[k]) == at(iter, next[k])
                    };
                    0 <= cur;
                    cur < n;
                    separate(memory(next[0..n]), memory(visited[0..n]));
                }
                assumption();
            }
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
