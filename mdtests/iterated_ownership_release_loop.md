# Iterated ownership: releasing a run in reverse

`release_run` walks a claimed run `[start, end)` from its top, clearing one
occupancy flag per iteration. It is the reverse of
[`iterated_ownership_claim_loop.md`](iterated_ownership_claim_loop.md) over
the same `arena_window`: the window owns the claimed cells `[start, next)`
and knows `[next, end)` is free, and each iteration moves `next` one cell
down.

The store `occupied[i] = 0` writes a guard cell while the window owns the
element `data[i]` outright, so the iterated fact cannot hold it and the store
rule opens a hole at `i`. The stored value makes the guard true, so the hole
stays open until `give(data[i..i + 1])` moves the element back into the fact.
The proof then extends the free range by one cell: the new cell from the
store, the rest transported across it.

`src/surface/tests/expansion_tests.rs` expands this fixture's proof and
reverifies the result; `click audit` agrees.

```c filename=iterated_ownership_release_loop.c
void release_run(int32* data, int32* occupied, int32 capacity, int32 start, int32 end) {
    int32 i;
    i = end;
    while (i > start) {
        i = i - 1;
        occupied[i] = 0;
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

verifying "iterated_ownership_release_loop.c";

void release_run(int32* data, int32* occupied, int32 capacity, int32 start, int32 end) {
    owns w: arena_window(data, occupied, capacity, start, end);
    requires w.next == end;
    requires start <= end;
    ensures w.next == start;
} by {
    step();
    step();
    loop {
        owns w: arena_window(data, occupied, capacity, start, end);
        invariant w.next == i;
        invariant start <= i;
        decreases i - start;

        initialize by simp;
        preserve by {
            let { next: n } = unfold(w);
            have n == i by simp;
            have start < i by simp;
            have i <= end by simp;
            have end <= capacity by simp;
            have 0 <= start by simp;
            have 0 <= i by simp;
            mark opened;
            step();
            have start <= i by {
                arithmetic() using {
                    start < at(opened, i);
                    0 <= start;
                }
            }
            have 0 <= i by simp;
            step();
            give(data[i..i + 1]);
            have forall (k: int32) {
                i <= k and k < end implies occupied[k] == 0
            } by {
                intro();
                intro();
                extract(i <= k);
                extract(k < end);
                if i < k {
                    apply(int32_increment_upper_bound(i, k)) using { i < k; }
                    have n <= k by {
                        rewrite(n == at(opened, i));
                        assumption();
                    }
                    have at(opened, occupied[k]) == 0 by {
                        instantiate(forall (k: int32) {
                            n <= k and k < end implies at(opened, occupied[k]) == 0
                        }, k) using {
                            n <= k;
                            k < end;
                        }
                        assumption();
                    }
                    apply(int32_le_lt_transitive(0, i, k)) using { 0 <= i; i < k; }
                    apply(int32_lt_implies_le(0, k)) using { 0 < k; }
                    apply(int32_lt_le_transitive(k, end, capacity)) using {
                        k < end;
                        end <= capacity;
                    }
                    apply(int32_lt_transitive(i, k, capacity)) using { i < k; k < capacity; }
                    transport(
                        at(opened, occupied[k]) == 0,
                        occupied[k] == 0
                    ) using {
                        at(opened, occupied[k]) == 0;
                        i < k;
                        0 <= i;
                        i < capacity;
                        0 <= k;
                        k < capacity;
                    }
                    assumption();
                } else {
                    have i == k by {
                        apply(int32_le_and_not_lt_implies_eq(i, k)) using {
                            i <= k;
                            not (i < k);
                        }
                    }
                    have k == i by simp;
                    rewrite(k == i);
                    normalize();
                }
            }
            have at(opened, i) <= end by { assumption(); }
            have i <= end by {
                apply(int32_nonnegative_predecessor_upper_bound(at(opened, i), end)) using {
                    0 <= at(opened, i);
                    at(opened, i) <= end;
                }
                assumption();
            }
            let w = fold(arena_window(data, occupied, capacity, start, end), { next: i });
            have 0 <= 0 - start + at(statement(3).entry, i) - 1 by {
                arithmetic() using {
                    start < at(statement(3).entry, i);
                    0 <= start;
                }
            }
            have 0 - start + at(statement(3).entry, i) - 1
                < 0 - start + at(statement(3).entry, i) by {
                arithmetic() using {
                    start < at(statement(3).entry, i);
                    0 <= start;
                }
            }
            close_invariants();
        }
    }
    apply(int32_le_implies_reversed_ge(start, i)) using { start <= i; }
    apply(int32_ge_and_not_gt_implies_eq(i, start)) using {
        i >= start;
        not (i > start);
    }
    have w.next == start by {
        rewrite(w.next == i);
        rewrite(i == start);
        normalize();
    }
    execute();
    simp();
}
```

```expect
pass
```
