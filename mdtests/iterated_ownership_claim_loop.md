# Iterated ownership: claiming a run one element per iteration

`claim_run` marks every cell of the run `[start, end)` occupied and zeroes
it, and the caller receives the run as one `region`. The loop owns an
`arena_window`: the arena's occupancy map and its iterated ownership,
the cells `[start, next)` claimed so far, and the per-cell invariant that
every cell of `[next, end)` is still free. One iteration opens the window,
reads that the guard `occupied[i] == 0` holds at `i`, takes `data[i]` out
of the iterated fact, marks the cell (the store closes the hole the unfold
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

        initialize by close();
        maintain by {
            let { next: n } = unfold(w);
            have n == i;
            have n <= i;
            have i < end;
            have end <= capacity;
            have forall (k: int32) {
                to_integer(i + 1) <= to_integer(k) and k < end implies occupied[k] == 0
            } by {
                intro();
                intro();
                have to_integer(i + 1) <= to_integer(k);
                have i < i + 1;
                have i < k;
                have i <= k;
                have n <= k by {
                    rewrite(n, i);
                    close();
                }
                instantiate(forall (k: int32) {
                    n <= k and k < end implies occupied[k] == 0
                }, k);
                close();
            }
            have occupied[i] == 0 by {
                instantiate(forall (k: int32) {
                    n <= k and k < end implies occupied[k] == 0
                }, i);
                close();
            }
            unfold(arena_window(data, occupied, capacity, start, end)[i]);
            have start <= i;
            have 0 <= i;
            have i < capacity;
            mark opened;
            step();
            step();
            have forall (k: int32) {
                to_integer(at(opened, i) + 1) <= to_integer(k) and k < end implies occupied[k] == 0
            } by {
                intro();
                intro();
                have to_integer(at(opened, i) + 1) <= to_integer(k);
                have at(opened, occupied[k]) == 0 by {
                    instantiate(forall (k: int32) {
                        to_integer(at(opened, i) + 1) <= to_integer(k) and k < end implies at(opened, occupied[k]) == 0
                    }, k);
                    close();
                }
                have at(opened, i) < end;
                have at(opened, i) < at(opened, i) + 1;
                have at(opened, i) < k;
                have 0 <= at(opened, i) by close();
                have at(opened, i) < capacity by close();
                have 0 <= k;
                have k < capacity;
                have i < k by { close(); }
                have i != k by { close() using { i < k; }; }
                have separate(memory(occupied[i]), memory(occupied[k])) by {
                    apply(click::separation::separate_elements(occupied, i, k));
                }
                have separate(loop(0).statement(0).footprint, memory(occupied[k])) by {
                    close() using { separate(memory(occupied[i]), memory(occupied[k])); };
                }
                have at(loop(0).statement(0).exit, occupied[k]) == at(opened, occupied[k]) by {
                    preserve(memory(occupied[k]), loop(0).statement(0));
                }
                have contains(memory(data[0..capacity]), memory(data[i])) by {
                    apply(click::separation::contains_element(data, 0, capacity, i));
                }
                have contains(memory(occupied[0..capacity]), memory(occupied[k])) by {
                    apply(click::separation::contains_element(occupied, 0, capacity, k));
                }
                have separate(memory(data[0..capacity]), memory(occupied[0..capacity])) by {
                    apply(click::separation::separate_symm(memory(occupied[0..capacity]), memory(data[0..capacity])));
                }
                have separate(memory(data[i]), memory(occupied[k])) by {
                    apply(click::separation::separate_restrict(memory(data[0..capacity]), memory(occupied[0..capacity]), memory(data[i]), memory(occupied[k])));
                }
                have separate(loop(0).statement(1).footprint, memory(occupied[k])) by {
                    close() using { separate(memory(data[i]), memory(occupied[k])); };
                }
                have occupied[k] == at(loop(0).statement(1).entry, occupied[k]) by {
                    preserve(memory(occupied[k]), loop(0).statement(1));
                }
                close();
            }
            step();
            let w = fold(arena_window(data, occupied, capacity, start, end), {
                next: at(opened, i) + 1
            });
            have 0 <= to_integer(end - at(region(3).entry, i) - 1) by {
                close() using {
                    at(region(3).entry, i) < end;
                    0 <= at(region(3).entry, i);
                    end <= capacity;
                };
            }
            have to_integer(end - at(region(3).entry, i) - 1) < to_integer(end - at(region(3).entry, i)) by {
                close() using {
                    at(region(3).entry, i) < end;
                    0 <= at(region(3).entry, i);
                    end <= capacity;
                };
            }
        }
    }
    let { next: n } = unfold(w);
    step_until(function.exit);
    fold(arena_cells(data, occupied, capacity));
    fold(region(data, start, end));
    close();
}
```

```expect
pass
```
