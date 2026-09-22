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
        induct(fuel) as ih {
            Nat::Zero => {
                unfold(walk(next, from, Nat::Zero));
                simp();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                have 0 <= next[walk(next, from, previous)]
                    and next[walk(next, from, previous)] < n by {
                    instantiate(forall (k: int32) {
                        0 <= k and k < n implies 0 <= next[k] and next[k] < n
                    }, walk(next, from, previous)) using {
                        0 <= walk(next, from, previous);
                        walk(next, from, previous) < n;
                    }
                    assumption();
                }
                unfold(walk(next, from, Nat::Succ(previous)));
                assumption();
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
        induct(fuel) as ih {
            Nat::Zero => {
                unfold(walk(a, from, Nat::Zero));
                unfold(walk(b, from, Nat::Zero));
                normalize();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                have 0 <= n by { arithmetic() using { 0 <= from; from < n; } }
                have 0 <= n - 0 by { arithmetic() using { 0 <= n; } }
                have n - 0 <= 1073741823 by {
                    arithmetic() using { n <= 1073741823; }
                }
                apply(walk_in_range(a, n, from, previous)) using {
                    0 <= from;
                    from < n;
                    n <= 1073741823;
                    viewable(a[0..n]);
                    forall (k: int32) {
                        0 <= k and k < n implies 0 <= a[k] and a[k] < n
                    };
                    0 <= n - 0;
                    n - 0 <= 1073741823;
                }
                have a[walk(a, from, previous)] == b[walk(a, from, previous)] by {
                    instantiate(forall (k: int32) {
                        0 <= k and k < n implies a[k] == b[k]
                    }, walk(a, from, previous)) using {
                        0 <= walk(a, from, previous);
                        walk(a, from, previous) < n;
                    }
                    assumption();
                }
                unfold(walk(a, from, Nat::Succ(previous)));
                unfold(walk(b, from, Nat::Succ(previous)));
                simp() using {
                    walk(a, from, previous) == walk(b, from, previous);
                    a[walk(a, from, previous)] == b[walk(a, from, previous)];
                }
            }
        }
    }
}

void mark(int32 *next, int32 *visited) {
    views next[0..1];
    consumes visited[0..1];
    produces visited[0..1];
    requires separate(memory(next[0..1]), memory(visited[0..1]));
    requires next[0] == 0;
    requires walk(next, 0, Nat::Succ(Nat::Zero)) == 0;
    ensures walk(next, 0, Nat::Succ(Nat::Zero)) == 0;
} by {
    mark entry;
    have at(entry, next[0]) == 0 by { simp(); }
    step();
    have at(entry, next[0]) == next[0] by {
        have at(entry, next[0]) == at(entry, next[0]) by { normalize(); }
        transport(
            at(entry, next[0]) == at(entry, next[0]),
            at(entry, next[0]) == next[0]
        ) using {
            at(entry, next[0]) == at(entry, next[0]);
            separate(memory(next[0..1]), memory(visited[0..1]));
        }
        assumption();
    }
    have forall (k: int32) {
        0 <= k and k < 1 implies at(entry, next[k]) == next[k]
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < 1);
        have k == 0 by { arithmetic() using { 0 <= k; k < 1; } }
        simp() using { k == 0; at(entry, next[0]) == next[0]; }
    }
    have forall (k: int32) {
        0 <= k and k < 1 implies
            0 <= at(entry, next[k]) and at(entry, next[k]) < 1
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < 1);
        have k == 0 by { arithmetic() using { 0 <= k; k < 1; } }
        have at(entry, next[k]) == 0 by {
            rewrite(k == 0);
            assumption();
        }
        have 0 <= at(entry, next[k]) by {
            arithmetic() using { at(entry, next[k]) == 0; }
        }
        have at(entry, next[k]) < 1 by {
            arithmetic() using { at(entry, next[k]) == 0; }
        }
        split();
    }
    have at(entry, viewable(next[0..1])) by { simp(); }
    have viewable(next[0..1]) by { simp(); }
    have 0 <= 0 by { simp(); }
    have 0 < 1 by { simp(); }
    have 1 <= 1073741823 by { simp(); }
    have 0 <= 1 - 0 by { simp(); }
    have 1 - 0 <= 1073741823 by { simp(); }
    apply(walk_frame(at(entry, next), next, 1, 0, Nat::Succ(Nat::Zero))) using {
        0 <= 0;
        0 < 1;
        1 <= 1073741823;
        at(entry, viewable(next[0..1]));
        viewable(next[0..1]);
        forall (k: int32) {
            0 <= k and k < 1 implies
                0 <= at(entry, next[k]) and at(entry, next[k]) < 1
        };
        forall (k: int32) {
            0 <= k and k < 1 implies at(entry, next[k]) == next[k]
        };
        0 <= 1 - 0;
        1 - 0 <= 1073741823;
    }
    have at(entry, walk(next, 0, Nat::Succ(Nat::Zero))) == 0 by { simp(); }
    have walk(next, 0, Nat::Succ(Nat::Zero)) == 0 by {
        simp() using {
            at(entry, walk(next, 0, Nat::Succ(Nat::Zero))) == 0;
            walk(at(entry, next), 0, Nat::Succ(Nat::Zero))
                == walk(next, 0, Nat::Succ(Nat::Zero));
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
