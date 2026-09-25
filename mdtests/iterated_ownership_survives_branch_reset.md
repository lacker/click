# Iterated ownership: an iterated fact survives a loop whose branch rewrites a local

`scan_run` walks the occupancy map counting the current run of free cells,
as the arena's first-fit scan does. Its loop owns an `arena_scan` window
that carries the map, the iterated ownership of the free cells, and the run
found so far. One arm of the body resets the run to the constant `0`.

A memory snapshot is interned by content, and the first derivation recorded
for a content keeps being its history. The reset can produce a snapshot
whose content an earlier path already recorded, so its history does not
pass through the snapshot the step started from. The iterated fact is kept
across a store only when the store provably misses its guard cells, and a
walk of that unrelated history met stores to the arena's own cells and
dropped the fact, so the window no longer folded. The walk now steps both
snapshots back to their common ancestor and ignores a store that leaves its
cell unchanged between them.

```c filename=iterated_ownership_survives_branch_reset.c
struct arena {
    int32* data;
    int32* occupied;
    int32 capacity;
    int32 live_regions;
};

int32 scan_run(struct arena* arena, int32 count) {
    int32 i;
    int32 run_length;

    i = 0;
    run_length = 0;
    while (i < arena->capacity && run_length < count) {
        if (arena->occupied[i] == 0) {
            run_length = run_length + 1;
        } else {
            run_length = 0;
        }
        i = i + 1;
    }
    return run_length;
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

resource arena_scan(data: int32*, occupied: int32*, capacity: int32) {
    field lo: int32;
    field hi: int32;
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
    fact 0 <= lo;
    fact lo <= hi;
    fact hi <= capacity;
    fact forall (k: int32) {
        lo <= k and k < hi implies occupied[k] == 0
    };
}

verifying "iterated_ownership_survives_branch_reset.c";

int32 scan_run(struct arena* arena, int32 count) {
    owns object(arena);
    owns arena_cells(arena->data, arena->occupied, arena->capacity);
    requires 0 < count;
    requires count <= arena->capacity;
    requires arena->capacity <= 536870911;
    requires separate(
        memory(object(arena)),
        memory(arena->occupied[0..arena->capacity])
    );
    requires separate(
        memory(object(arena)),
        memory(arena->data[0..arena->capacity])
    );
} by {
    unfold(arena_cells(arena->data, arena->occupied, arena->capacity));
    step();
    step();
    step();
    step();
    have 0 <= arena->capacity by {
        arithmetic() using {
            0 < count;
            count <= arena->capacity;
        }
    }
    have forall (k: int32) {
        0 <= k and k < 0 implies arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < 0);
        have not (k < 0) by {
            arithmetic() using { 0 <= k; }
        }
        contradiction(k < 0);
    }
    let run = fold(arena_scan(arena->data, arena->occupied, arena->capacity), {
        lo: 0, hi: 0
    });
    loop as find_first_free_run {
        decreases arena->capacity - i;
        owns run: arena_scan(arena->data, arena->occupied, arena->capacity);
        invariant run.hi == i;
        invariant run.lo + run_length == i;
        invariant 0 <= run_length and run_length <= count;

        initialize by simp;
        preserve by {
            mark iteration;
            let { lo: lo, hi: hi } = unfold(run);
            have hi == i by {
                simp();
            }
            have lo + run_length == i by {
                simp();
            }
            have lo <= i by {
                simp() using {
                    lo <= hi;
                    hi == i;
                }
            }
            have 0 <= i by {
                apply(int32_le_transitive(0, lo, i)) using {
                    0 <= lo;
                    lo <= i;
                }
            }
            have i + 1 <= arena->capacity by {
                apply(int32_increment_upper_bound(i, arena->capacity)) using {
                    i < arena->capacity;
                }
            }
            if arena->occupied[i] == 0 {
                have run_length + 1 <= count by {
                    apply(int32_increment_upper_bound(run_length, count)) using {
                        run_length < count;
                    }
                }
                branch {
                    then {
                        step();
                    }
                    else {
                        contradiction(not (arena->occupied[i] == 0));
                    }
                }
                step();
                have forall (k: int32) {
                    lo <= k and k < i implies arena->occupied[k] == 0
                } by {
                    intro();
                    intro();
                    extract(lo <= k);
                    extract(k < i);
                    if k < at(iteration, i) {
                        have k < hi by {
                            simp();
                        }
                        instantiate(forall (j: int32) {
                            lo <= j and j < hi implies arena->occupied[j] == 0
                        }, k) using {
                            lo <= k;
                            k < hi;
                        }
                        assumption();
                    } else {
                        have i == at(iteration, i) + 1 by {
                            normalize();
                        }
                        have k < at(iteration, i) + 1 by {
                            rewrite(i == at(iteration, i) + 1);
                            assumption();
                        }
                        have k <= at(iteration, i) by {
                            apply(int32_lt_successor_implies_le(
                                k,
                                at(iteration, i)
                            )) using {
                                k < at(iteration, i) + 1;
                            }
                        }
                        have k == at(iteration, i) by {
                            apply(int32_le_and_not_lt_implies_eq(
                                k,
                                at(iteration, i)
                            )) using {
                                k <= at(iteration, i);
                                not (k < at(iteration, i));
                            }
                        }
                        rewrite(k == at(iteration, i));
                        assumption();
                    }
                }
                have hi == at(iteration, i) by {
                    simp();
                }
                have i == at(iteration, i) + 1 by {
                    normalize();
                }
                have lo <= at(iteration, i) by {
                    simp() using {
                        lo <= hi;
                        hi == at(iteration, i);
                    }
                }
                have at(iteration, i) < at(iteration, i) + 1 by {
                    apply(int32_increment_strictly_increases(
                        at(iteration, i),
                        at(iteration, arena->capacity)
                    )) using {
                        at(iteration, i) < at(iteration, arena->capacity);
                    }
                }
                have at(iteration, i) < i by {
                    rewrite(i == at(iteration, i) + 1);
                    assumption();
                }
                have at(iteration, i) <= i by {
                    apply(int32_lt_implies_le(at(iteration, i), i)) using {
                        at(iteration, i) < i;
                    }
                }
                have lo <= i by {
                    apply(int32_le_transitive(lo, at(iteration, i), i)) using {
                        lo <= at(iteration, i);
                        at(iteration, i) <= i;
                    }
                }
                have i <= arena->capacity by {
                    simp();
                }
                have run_length == at(iteration, run_length) + 1 by {
                    normalize();
                }
                have lo + at(iteration, run_length) == at(iteration, i) by {
                    simp();
                }
                have lo + run_length == i by {
                    rewrite(run_length == at(iteration, run_length) + 1);
                    rewrite(i == at(iteration, i) + 1);
                    simp();
                }
                have 0 <= run_length and run_length <= count by {
                    simp();
                }
                let run = fold(arena_scan(arena->data, arena->occupied, arena->capacity), {
                    lo: lo, hi: i
                });
                have run.hi == i by {
                    simp();
                }
                have run.lo + run_length == i by {
                    simp();
                }
                have 0 <= at(iteration, i) by {
                    assumption();
                }
                have 0 <= 0 - at(iteration, i) + arena->capacity - 1 by {
                    arithmetic() using {
                        0 <= at(iteration, i);
                        at(iteration, i) < at(iteration, arena->capacity);
                        0 <= arena->capacity;
                    }
                }
                have 0 - at(iteration, i) + arena->capacity - 1
                    < 0 - at(iteration, i) + arena->capacity by {
                    arithmetic() using {
                        0 <= at(iteration, i);
                        at(iteration, i) < at(iteration, arena->capacity);
                        0 <= arena->capacity;
                    }
                }
                close_invariants();
            } else {
                branch {
                    then {
                        contradiction(arena->occupied[i] == 0);
                    }
                    else {
                        step();
                    }
                }
                step();
                have forall (k: int32) {
                    i <= k and k < i implies arena->occupied[k] == 0
                } by {
                    intro();
                    intro();
                    extract(i <= k);
                    extract(k < i);
                    have not (k < i) by {
                        arithmetic() using { i <= k; }
                    }
                    contradiction(k < i);
                }
                have 0 <= i by { simp(); }
                have i <= arena->capacity by { simp(); }
                let run = fold(arena_scan(arena->data, arena->occupied, arena->capacity), {
                    lo: i, hi: i
                });
                have 0 <= at(iteration, i) by {
                    assumption();
                }
                have 0 <= 0 - at(iteration, i) + arena->capacity - 1 by {
                    arithmetic() using {
                        0 <= at(iteration, i);
                        at(iteration, i) < at(iteration, arena->capacity);
                        0 <= arena->capacity;
                    }
                }
                have 0 - at(iteration, i) + arena->capacity - 1
                    < 0 - at(iteration, i) + arena->capacity by {
                    arithmetic() using {
                        0 <= at(iteration, i);
                        at(iteration, i) < at(iteration, arena->capacity);
                        0 <= arena->capacity;
                    }
                }
                close_invariants();
            }
        }
    }
    let { lo: run_lo, hi: run_hi } = unfold(run);
    fold(arena_cells(arena->data, arena->occupied, arena->capacity));
    execute();
    simp();
}
```

```expect
pass
```
