# A symbolic array load remains on the loop store's history

The loop reads a symbolic `next[cur]` after writing the disjoint `visited`
array. Every guarded `next[k]` value should retain its iteration-entry value.
An unrelated existential fact keeps the proof on the explicit transport path;
that path needs bounds for both the read index `k` and the write index `cur`.

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
                intro();
                intro();
                extract(0 <= k);
                extract(k < n);
                have at(iter, next[k]) == at(iter, next[k]) by { normalize(); }
                transport(
                    at(iter, next[k]) == at(iter, next[k]),
                    at(iter, next[k]) == next[k]
                ) using {
                    at(iter, next[k]) == at(iter, next[k]);
                    0 <= k;
                    k < n;
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
