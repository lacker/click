# A pointer-chasing search terminates on the number of unmarked cells

`next` holds quasi-pointers: every entry of `next[0..n]` is itself an index
into `0..n`. The search follows those entries, marking each cell it leaves,
and stops when it reaches a cell it has already marked.

Nothing about the indices decreases, so the loop measure is the number of
cells in `visited[0..n]` that still hold zero. The guard establishes that the
current cell contributes one; the body marks it and the point-update theorem
proves that the measure drops by exactly one. The proof also exercises an
early return inside the ranked loop. Explicit cell separation preserves the
quantified bounds on the pointer-chasing array and the two parts of the
mark array beside the store. A ghost `Nat` witness tracks how many `next` hops reach
`cur`; its inductive frame lemma keeps that relation stable across each store
to the disjoint `visited` array. A result of `1` therefore names an in-bounds,
unmarked target reachable from `from` by a finite walk.

```c filename=search_terminates_by_unmarked_count.c
int32 search(int32 *next, int32 *visited, int32 n, int32 from, int32 to) {
    int32 cur = from;
    while (visited[cur] == 0) {
        if (cur == to) return 1;
        visited[cur] = 1;
        cur = next[cur];
    }
    return 0;
}
```

```click
verifying "search_terminates_by_unmarked_count.c";

import "unmarked_count_lemmas.click";

function walk(next: int32[], from: int32, fuel: Nat) -> int32 decreases fuel {
    match fuel {
        Nat::Zero => from,
        Nat::Succ(previous) => next[walk(next, from, previous)],
    }
}

theorem walk_in_range(next: int32[], n: int32, from: int32, fuel: Nat) {
    requires 0 <= from;
    requires from < n;
    requires n <= 1073741823;
    views next[0..n];
    requires forall (k: int32) {
        0 <= k and k < n implies 0 <= next[k] and next[k] < n
    };
    ensures 0 <= walk(next, from, fuel) and walk(next, from, fuel) < n by {
        let ih = induct(fuel);
        match fuel {
            Nat::Zero => {
                unfold(walk(next, from, Nat::Zero));
                close();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                have 0 <= next[walk(next, from, previous)]
                    and next[walk(next, from, previous)] < n by {
                    have 0 <= (walk(next, from, previous)) and (walk(next, from, previous)) < n;
                    instantiate(forall (k: int32) {
                        0 <= k and k < n implies 0 <= next[k] and next[k] < n
                    }, walk(next, from, previous));
                    close();
                }
                unfold(walk(next, from, Nat::Succ(previous)));
                close();
            }
        }
    }
}

theorem walk_frame(a: int32[], b: int32[], n: int32, from: int32, fuel: Nat) {
    requires 0 <= from;
    requires from < n;
    requires n <= 1073741823;
    views a[0..n];
    views b[0..n];
    requires forall (k: int32) {
        0 <= k and k < n implies 0 <= a[k] and a[k] < n
    };
    requires forall (k: int32) {
        0 <= k and k < n implies a[k] == b[k]
    };
    ensures walk(a, from, fuel) == walk(b, from, fuel) by {
        let ih = induct(fuel);
        match fuel {
            Nat::Zero => {
                unfold(walk(a, from, Nat::Zero));
                unfold(walk(b, from, Nat::Zero));
                close();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                apply(walk_in_range(a, n, from, previous));
                have a[walk(a, from, previous)] == b[walk(a, from, previous)] by {
                    have 0 <= (walk(a, from, previous)) and (walk(a, from, previous)) < n;
                    instantiate(forall (k: int32) {
                        0 <= k and k < n implies a[k] == b[k]
                    }, walk(a, from, previous));
                    close();
                }
                unfold(walk(a, from, Nat::Succ(previous)));
                unfold(walk(b, from, Nat::Succ(previous)));
                close() using {
                    walk(a, from, previous) == walk(b, from, previous);
                    a[walk(a, from, previous)] == b[walk(a, from, previous)];
                };
            }
        }
    }
}

int32 search(int32 *next, int32 *visited, int32 n, int32 from, int32 to) {
    requires 0 <= from;
    requires from < n;
    requires n <= 1073741823;
    views next[0..n];
    owns visited[0..n];
    requires separate(memory(next[0..n]), memory(visited[0..n]));
    requires forall (k: int32) {
        0 <= k and k < n implies 0 <= next[k] and next[k] < n
    };
    ensures result == 1 implies
        0 <= to and to < n and visited[to] == 0;
    ensures result == 1 implies
        exists (fuel: Nat) { walk(next, from, fuel) == to };
} by {
    step();
    step();
    have exists (fuel: Nat) { walk(next, from, fuel) == cur } by {
        witness(Nat::Zero);
        unfold(walk(next, from, Nat::Zero));
        close();
    }
    loop {
        decreases unmarked(visited, 0, n);
        invariant 0 <= cur;
        invariant cur < n;
        invariant forall (k: int32) {
            0 <= k and k < n implies 0 <= next[k] and next[k] < n
        };
        invariant exists (fuel: Nat) { walk(next, from, fuel) == cur };
        views next[0..n];
        owns visited[0..n];
        initialize by { close(); }
        maintain by {
            observe(visited[0..n]);
            mark iter;
            let previous = obtain(exists (previous: Nat) { walk(next, from, previous) == cur });
            have at(iter, forall (k: int32) {
                0 <= k and k < n implies 0 <= next[k] and next[k] < n
            }) by { close(); }
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
            have forall (k: int32) { 0 <= k and k < cur implies at(iter, visited[k]) == visited[k] } by {
                intro(); intro();
                have cur != k by { close() using { k < cur; }; }
                have separate(memory(visited[cur]), memory(visited[k])) by {
                    apply(click::separation::separate_elements(visited, cur, k));
                }
                have separate(loop(0).statement(1).footprint, memory(visited[k])) by {
                    close() using { separate(memory(visited[cur]), memory(visited[k])); };
                }
                have visited[k] == at(iter, visited[k]) by {
                    preserve(memory(visited[k]), loop(0).statement(1));
                }
                close();
            }
            have forall (k: int32) { cur < k and k < n implies at(iter, visited[k]) == visited[k] } by {
                intro(); intro();
                have cur != k by { close() using { cur < k; }; }
                have separate(memory(visited[cur]), memory(visited[k])) by {
                    apply(click::separation::separate_elements(visited, cur, k));
                }
                have separate(loop(0).statement(1).footprint, memory(visited[k])) by {
                    close() using { separate(memory(visited[cur]), memory(visited[k])); };
                }
                have visited[k] == at(iter, visited[k]) by {
                    preserve(memory(visited[k]), loop(0).statement(1));
                }
                close();
            }
            observe(visited[0..n]);
            apply(unmarked_point_update(at(iter, visited), visited, 0, n, n, cur));
            apply(unmarked_nonnegative(visited, 0, n, n));
            have unmarked(visited, 0, n) < unmarked(at(iter, visited), 0, n) by {
                close() using {
                    to_integer(unmarked(visited, 0, n)) == to_integer(unmarked(at(iter, visited), 0, n) - 1);
                };
            }
            have 0 <= next[cur] and next[cur] < n by {
                instantiate(forall (k: int32) {
                    0 <= k and k < n implies 0 <= next[k] and next[k] < n
                }, cur);
                close();
            }
            step();
            observe(next[0..n]);
            apply(walk_frame(at(iter, next), next, n, from, previous));
            have walk(next, from, previous) == at(iter, cur) by {
                close() using {
                    at(iter, walk(next, from, previous)) == at(iter, cur);
                    walk(at(iter, next), from, previous) == walk(next, from, previous);
                };
            }
            have next[walk(next, from, previous)] == next[at(iter, cur)] by {
                close() using { walk(next, from, previous) == at(iter, cur); };
            }
            have exists (fuel: Nat) { walk(next, from, fuel) == cur } by {
                witness(Nat::Succ(previous));
                unfold(walk(next, from, Nat::Succ(previous)));
            }
        }
    }
}
```

```expect
pass
```
