# Iterated ownership: claiming a run one element per iteration

`claim_run` marks every cell of the run `[start, end)` occupied and zeroes
it, and the caller receives the run as one `region`. The loop owns an
`arena_window`: the arena's occupancy map and its iterated ownership,
the cells `[start, next)` claimed so far, and the per-cell invariant that
every cell of `[next, end)` is still free. One iteration opens the window,
reads that the guard `occupied[i] == 0` holds at `i`, takes `data[i]` out
of the iterated fact, marks the cell (the store closes the hole the take
opened, because `1` makes the guard false), zeroes it, and refolds the window
one cell later. Each iteration's resource steps read one guard cell and one
element; the fact's range is never enumerated.

After the loop the window splits into `arena_cells`, whose iterated fact no
longer claims the run, and the claimed cells `data[start..end]`, folded as
the caller's `region`.

`src/surface/tests/expansion_tests.rs` expands this fixture's proof and
reverifies the result; `click audit` agrees.

```c filename=iterated_ownership_claim_loop.c
void claim_run(int32* data, int32* occupied, int32 capacity, int32 start, int32 end) {
    int32 i;
    i = start;
    while (i < end) {
        occupied[i] = 1;
        data[i] = 0;
        i = i + 1;
    }
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

verifying "iterated_ownership_claim_loop.c";

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
```

```expect
pass
```
