# Iterated ownership: freed cells are reused by a larger run

The occupancy map is the whole free-list, so freeing needs no merge step and
reusing freed space needs no defragmentation. `recycle_ba` and `recycle_ab`
each hold two claimed cells `a` and `b` that are not adjacent, and know the
gap `[a + 1, b)` between them is free. They clear both flags, in either
order, give both elements back, and immediately claim the larger run
`[a, b + 1)` that spans the two freed cells and the gap, through the
verified loop [`claim_run`](iterated_ownership_claim_loop.md). The only
proof work is the per-cell fact that the new run is free, assembled from the
two stores and the gap.

```c filename=iterated_ownership_coalescing.c
void claim_run(int32* data, int32* occupied, int32 capacity, int32 start, int32 end) {
    int32 i;
    i = start;
    while (i < end) {
        occupied[i] = 1;
        data[i] = 0;
        i = i + 1;
    }
}

void recycle_ba(int32* data, int32* occupied, int32 capacity, int32 a, int32 b) {
    occupied[b] = 0;
    occupied[a] = 0;
    claim_run(data, occupied, capacity, a, b + 1);
}

void recycle_ab(int32* data, int32* occupied, int32 capacity, int32 a, int32 b) {
    occupied[a] = 0;
    occupied[b] = 0;
    claim_run(data, occupied, capacity, a, b + 1);
}
```

```click
resource arena_cells(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
}

resource arena_window(data: int32*, occupied: int32*, capacity: int32, start: int32, end: int32) {
    field next: int32;
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
    owns data[start..next];
    fact 0 <= start;
    fact start <= next;
    fact next <= end;
    fact end <= capacity;
    fact separate(memory(occupied[0..capacity]), memory(data[0..capacity]));
    fact forall (k: int32) {
        next <= k and k < end implies occupied[k] == 0
    };
}

resource region(data: int32*, start: int32, end: int32) {
    owns data[start..end];
}

verifying "iterated_ownership_coalescing.c";

void claim_run(int32* data, int32* occupied, int32 capacity, int32 start, int32 end) {
    consumes w: arena_window(data, occupied, capacity, start, end);
    requires w.next == start;
    produces arena_cells(data, occupied, capacity);
    produces region(data, start, end);
} by {
    step();
    step();
    loop {
        owns w: arena_window(data, occupied, capacity, start, end);
        invariant w.next == i;
        decreases end - i;

        initialize by simp;
        preserve by {
            let { next: n } = unfold(w);
            have n == i by simp;
            have n <= i by simp;
            have i < end by simp;
            have end <= capacity by simp;
            have forall (k: int32) {
                i + 1 <= k and k < end implies occupied[k] == 0
            } by {
                intro();
                intro();
                extract(i + 1 <= k);
                extract(k < end);
                apply(int32_increment_strictly_increases(i, end)) using {
                    i < end;
                }
                apply(int32_successor_le_implies_lt(i, k)) using {
                    i < i + 1;
                    i + 1 <= k;
                }
                apply(int32_lt_implies_le(i, k)) using {
                    i < k;
                }
                have n <= k by {
                    rewrite(n == i);
                    assumption();
                }
                instantiate(forall (k: int32) {
                    n <= k and k < end implies occupied[k] == 0
                }, k) using {
                    n <= k;
                    k < end;
                }
                assumption();
            }
            have occupied[i] == 0 by {
                instantiate(forall (k: int32) {
                    n <= k and k < end implies occupied[k] == 0
                }, i) using {
                    n <= i;
                    i < end;
                }
                assumption();
            }
            take(data[i..i + 1]);
            have start <= i by simp;
            have 0 <= i by simp;
            have i < capacity by simp;
            mark opened;
            step();
            step();
            have forall (k: int32) {
                at(opened, i) + 1 <= k and k < end implies occupied[k] == 0
            } by {
                intro();
                intro();
                extract(at(opened, i) + 1 <= k);
                extract(k < end);
                have at(opened, occupied[k]) == 0 by {
                    instantiate(forall (k: int32) {
                        at(opened, i) + 1 <= k and k < end implies at(opened, occupied[k]) == 0
                    }, k) using {
                        at(opened, i) + 1 <= k;
                        k < end;
                    }
                    assumption();
                }
                have at(opened, i) < end by simp;
                apply(int32_increment_strictly_increases(at(opened, i), end)) using {
                    at(opened, i) < end;
                }
                apply(int32_successor_le_implies_lt(at(opened, i), k)) using {
                    at(opened, i) < at(opened, i) + 1;
                    at(opened, i) + 1 <= k;
                }
                have 0 <= at(opened, i) by { assumption(); }
                have at(opened, i) < capacity by { assumption(); }
                have 0 <= k by simp;
                have k < capacity by simp;
                transport(
                    at(opened, occupied[k]) == 0,
                    occupied[k] == 0
                ) using {
                    at(opened, occupied[k]) == 0;
                    at(opened, i) < k;
                    0 <= at(opened, i);
                    at(opened, i) < capacity;
                    0 <= k;
                    k < capacity;
                    separate(memory(occupied[0..capacity]), memory(data[0..capacity]));
                }
                assumption();
            }
            step();
            let w = fold(arena_window(data, occupied, capacity, start, end), {
                next: at(opened, i) + 1
            });
            have 0 <= end - at(statement(3).entry, i) - 1 by {
                arithmetic() using {
                    at(statement(3).entry, i) < end;
                    0 <= at(statement(3).entry, i);
                    end <= capacity;
                }
            }
            have end - at(statement(3).entry, i) - 1 < end - at(statement(3).entry, i) by {
                arithmetic() using {
                    at(statement(3).entry, i) < end;
                    0 <= at(statement(3).entry, i);
                    end <= capacity;
                }
            }
            close_invariants();
        }
    }
    let { next: n } = unfold(w);
    execute();
    fold(arena_cells(data, occupied, capacity));
    fold(region(data, start, end));
    simp();
}
void recycle_ba(int32* data, int32* occupied, int32 capacity, int32 a, int32 b) {
    consumes gap: arena_window(data, occupied, capacity, a + 1, b);
    consumes region(data, a, a + 1);
    consumes region(data, b, b + 1);
    requires gap.next == a + 1;
    requires 0 <= a;
    requires a + 1 < b;
    requires b < capacity;
    produces arena_cells(data, occupied, capacity);
    produces region(data, a, b + 1);
} by {
    let { next: n } = unfold(gap);
    have n == a + 1 by simp;
    unfold(region(data, a, a + 1));
    unfold(region(data, b, b + 1));
    mark opened;
    step();
    step();
    give(data[b..b + 1]);
    give(data[a..a + 1]);
    have forall (k: int32) {
        a <= k and k < b + 1 implies occupied[k] == 0
    } by {
        intro();
        intro();
        extract(a <= k);
        extract(k < b + 1);
        if a < k {
            if k < b {
                apply(int32_increment_upper_bound(a, k)) using { a < k; }
                have n <= k by {
                    rewrite(n == a + 1);
                    assumption();
                }
                have at(opened, occupied[k]) == 0 by {
                    instantiate(forall (k: int32) {
                        n <= k and k < b implies at(opened, occupied[k]) == 0
                    }, k) using {
                        n <= k;
                        k < b;
                    }
                    assumption();
                }
                apply(int32_le_lt_transitive(0, a, k)) using { 0 <= a; a < k; }
                apply(int32_lt_implies_le(0, k)) using { 0 < k; }
                apply(int32_lt_transitive(k, b, capacity)) using { k < b; b < capacity; }
                apply(int32_lt_transitive(a, k, capacity)) using { a < k; k < capacity; }
                apply(int32_lt_implies_neq(a, k)) using { a < k; }
                apply(int32_lt_implies_neq(k, b)) using { k < b; }
                transport(
                    at(opened, occupied[k]) == 0,
                    occupied[k] == 0
                ) using {
                    at(opened, occupied[k]) == 0;
                    a < k;
                    k < b;
                    0 <= a;
                    a < capacity;
                    b < capacity;
                    0 <= k;
                    k < capacity;
                }
                assumption();
            } else {
                apply(int32_lt_successor_implies_le(k, b)) using { k < b + 1; }
                apply(int32_le_and_not_lt_implies_eq(k, b)) using { k <= b; not (k < b); }
                rewrite(k == b);
                normalize();
            }
        } else {
            apply(int32_le_and_not_lt_implies_eq(a, k)) using { a <= k; not (a < k); }
            have k == a by simp;
            rewrite(k == a);
            normalize();
        }
    }
    let w = fold(arena_window(data, occupied, capacity, a, b + 1), { next: a });
    step(claim_run(data, occupied, capacity, a, b + 1), { w: w });
    execute();
    simp();
}

void recycle_ab(int32* data, int32* occupied, int32 capacity, int32 a, int32 b) {
    consumes gap: arena_window(data, occupied, capacity, a + 1, b);
    consumes region(data, a, a + 1);
    consumes region(data, b, b + 1);
    requires gap.next == a + 1;
    requires 0 <= a;
    requires a + 1 < b;
    requires b < capacity;
    produces arena_cells(data, occupied, capacity);
    produces region(data, a, b + 1);
} by {
    let { next: n } = unfold(gap);
    have n == a + 1 by simp;
    unfold(region(data, a, a + 1));
    unfold(region(data, b, b + 1));
    mark opened;
    step();
    step();
    give(data[a..a + 1]);
    give(data[b..b + 1]);
    have forall (k: int32) {
        a <= k and k < b + 1 implies occupied[k] == 0
    } by {
        intro();
        intro();
        extract(a <= k);
        extract(k < b + 1);
        if a < k {
            if k < b {
                apply(int32_increment_upper_bound(a, k)) using { a < k; }
                have n <= k by {
                    rewrite(n == a + 1);
                    assumption();
                }
                have at(opened, occupied[k]) == 0 by {
                    instantiate(forall (k: int32) {
                        n <= k and k < b implies at(opened, occupied[k]) == 0
                    }, k) using {
                        n <= k;
                        k < b;
                    }
                    assumption();
                }
                apply(int32_le_lt_transitive(0, a, k)) using { 0 <= a; a < k; }
                apply(int32_lt_implies_le(0, k)) using { 0 < k; }
                apply(int32_lt_transitive(k, b, capacity)) using { k < b; b < capacity; }
                apply(int32_lt_transitive(a, k, capacity)) using { a < k; k < capacity; }
                apply(int32_lt_implies_neq(a, k)) using { a < k; }
                apply(int32_lt_implies_neq(k, b)) using { k < b; }
                transport(
                    at(opened, occupied[k]) == 0,
                    occupied[k] == 0
                ) using {
                    at(opened, occupied[k]) == 0;
                    a < k;
                    k < b;
                    0 <= a;
                    a < capacity;
                    b < capacity;
                    0 <= k;
                    k < capacity;
                }
                assumption();
            } else {
                apply(int32_lt_successor_implies_le(k, b)) using { k < b + 1; }
                apply(int32_le_and_not_lt_implies_eq(k, b)) using { k <= b; not (k < b); }
                rewrite(k == b);
                normalize();
            }
        } else {
            apply(int32_le_and_not_lt_implies_eq(a, k)) using { a <= k; not (a < k); }
            have k == a by simp;
            rewrite(k == a);
            normalize();
        }
    }
    let w = fold(arena_window(data, occupied, capacity, a, b + 1), { next: a });
    step(claim_run(data, occupied, capacity, a, b + 1), { w: w });
    execute();
    simp();
}
```

```expect
pass
```
