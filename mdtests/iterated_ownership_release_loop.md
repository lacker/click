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
stays open until `fold(arena_window(data, occupied, capacity, start, end)[i])` moves the element back into the fact.
The proof then extends the free range by one cell: the new cell from the
store, the rest preserved explicitly across the decrement and store before
restoring the slot with indexed `fold`.

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

        initialize by close();
        maintain by {
            let { next: n } = unfold(w);
            have n == i;
            have start < i;
            have i <= end;
            have end <= capacity;
            have 0 <= start;
            have 0 <= i;
            mark opened;
            step();
            have start <= i by {
                close() using {
                    start < at(opened, i);
                    0 <= start;
                };
            }
            have 0 <= i;
            step();
            have forall (k: int32) {
                i <= k and k < end implies occupied[k] == 0
            } by {
                intro();
                intro();
                if i < k {
                    have to_integer(i + 1) <= to_integer(k);
                    have n <= k by {
                        rewrite(n, at(opened, i));
                        close();
                    }
                    have at(opened, occupied[k]) == 0 by {
                        instantiate(forall (k: int32) {
                            n <= k and k < end implies at(opened, occupied[k]) == 0
                        }, k);
                        close();
                    }
                    have 0 < k;
                    have 0 <= k;
                    have k < capacity;
                    have i < capacity;
                    have separate(loop(0).statement(0).footprint, memory(occupied[k])) by {
                        close() using { };
                    }
                    have at(loop(0).statement(0).exit, occupied[k]) == at(opened, occupied[k]) by {
                        preserve(memory(occupied[k]), loop(0).statement(0));
                    }
                    have i != k by { close() using { i < k; }; }
                    have separate(memory(occupied[i]), memory(occupied[k])) by {
                        apply(click::separation::separate_elements(occupied, i, k));
                    }
                    have separate(loop(0).statement(1).footprint, memory(occupied[k])) by {
                        close() using { separate(memory(occupied[i]), memory(occupied[k])); };
                    }
                    have occupied[k] == at(loop(0).statement(1).entry, occupied[k]) by {
                        preserve(memory(occupied[k]), loop(0).statement(1));
                    }
                    close();
                } else {
                    have i == k;
                    have k == i;
                    rewrite(k, i);
                    close();
                }
            }
            have at(opened, i) <= end by close();
            have i <= end by {
                have to_integer(at(opened, i) - 1) <= to_integer(end);
                close();
            }
            fold(arena_window(data, occupied, capacity, start, end)[i]);
            let w = fold(arena_window(data, occupied, capacity, start, end), { next: i });
            have 0 <= to_integer(0 - start + at(region(3).entry, i) - 1) by {
                close() using {
                    start < at(region(3).entry, i);
                    0 <= start;
                };
            }
            have to_integer(0 - start + at(region(3).entry, i) - 1)
                < to_integer(0 - start + at(region(3).entry, i)) by {
                close() using {
                    start < at(region(3).entry, i);
                    0 <= start;
                };
            }
        }
    }
    have i >= start;
    have i == start;
    have w.next == start by {
        rewrite(w.next, i);
        rewrite(i, start);
        close();
    }
}
```

```expect
pass
```
