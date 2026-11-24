# A recursive walk over `next` survives a store to `visited`

The C writes only the owned `visited` array. Its separate, viewed `next`
array is unchanged, so the same recursive walk value holds after the store.

```c filename=recursive_walk_survives_unrelated_store.c
void mark(int32 *next, int32 *visited) {
    visited[0] = 1;
}
```

```click
verifying "recursive_walk_survives_unrelated_store.c";

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

void mark(int32 *next, int32 *visited) {
    views next[0..1];
    owns visited[0..1];
    requires separate(memory(next[0..1]), memory(visited[0..1]));
    requires next[0] == 0;
    requires walk(next, 0, Nat::Succ(Nat::Zero)) == 0;
    ensures walk(next, 0, Nat::Succ(Nat::Zero)) == 0;
} by {
    mark entry;
    have at(entry, next[0]) == 0;
    step();
    have separate(statement(0).footprint, memory(next[0])) by {
        close() using { separate(memory(next[0..1]), memory(visited[0..1])); };
    }
    have next[0] == at(entry, next[0]) by {
        preserve(memory(next[0]), statement(0));
    }
    have at(entry, next[0]) == next[0] by { close(); }
    have forall (k: int32) {
        0 <= k and k < 1 implies at(entry, next[k]) == next[k]
    } by {
        intro();
        intro();
        have k == 0 by { close() using { 0 <= k; k < 1; }; }
        close() using { k == 0; at(entry, next[0]) == next[0]; };
    }
    have forall (k: int32) {
        0 <= k and k < 1 implies
            0 <= at(entry, next[k]) and at(entry, next[k]) < 1
    } by {
        intro();
        intro();
        have k == 0 by { close() using { 0 <= k; k < 1; }; }
        have at(entry, next[k]) == 0 by {
            rewrite(k, 0);
            close();
        }
        have 0 <= at(entry, next[k]) by {
            close() using { at(entry, next[k]) == 0; };
        }
        have at(entry, next[k]) < 1 by {
            close() using { at(entry, next[k]) == 0; };
        }
        close();
    }
    have at(entry, viewable(next[0..1]));
    have viewable(next[0..1]) by { observe(next[0..1]); }
    have 0 <= 0;
    have 0 < 1;
    have 1 <= 1073741823;
    have 0 <= 1 - 0;
    have 1 - 0 <= 1073741823;
    apply(walk_frame(at(entry, next), next, 1, 0, Nat::Succ(Nat::Zero)));
    have at(entry, walk(next, 0, Nat::Succ(Nat::Zero))) == 0;
    have walk(next, 0, Nat::Succ(Nat::Zero)) == 0 by {
        close() using {
            at(entry, walk(next, 0, Nat::Succ(Nat::Zero))) == 0;
            walk(at(entry, next), 0, Nat::Succ(Nat::Zero))
                == walk(next, 0, Nat::Succ(Nat::Zero));
        };
    }
}
```

```expect
pass
```
