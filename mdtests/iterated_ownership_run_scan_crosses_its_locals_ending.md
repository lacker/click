# Iterated ownership: a run scan crosses the end of its locals

`scan_run` counts the current run of free cells while a loop owns an
`arena_scan` window carrying the map, the iterated ownership of the free
cells, and the run's bounds as fields; one arm resets the run to `0`.

The then-arm reasons over state-relative order facts
(`at(iteration, i) < at(iteration, i) + 1` beside `i == at(iteration, i) + 1`),
which the context consistency check must examine without declaring the
context contradictory. At the return the function's locals end, and the
state after their lifetime ends has the same content as one recorded
before they were declared, so its history does not pass through the state
the step started from. Invalidating iterated facts across that step must walk
both sides back to their common ancestor rather than the later side alone.

```c filename=iterated_ownership_run_scan_crosses_its_locals_ending.c
int32 scan_run(int32* data, int32* occupied, int32 capacity) {
    int32 i;
    int32 run_length;

    i = 0;
    run_length = 0;
    while (i < capacity) {
        if (occupied[i] == 0) {
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
}

verifying "iterated_ownership_run_scan_crosses_its_locals_ending.c";

int32 scan_run(int32* data, int32* occupied, int32 capacity) {
    owns arena_cells(data, occupied, capacity);
    requires 0 <= capacity;
} by {
    unfold(arena_cells(data, occupied, capacity));
    step();
    step();
    step();
    step();
    let run = fold(arena_scan(data, occupied, capacity), {
        lo: 0, hi: 0
    });
    loop as find_first_free_run {
        decreases capacity - i;
        owns run: arena_scan(data, occupied, capacity);
        invariant run.hi == i;
        invariant to_integer(run.lo + run_length) == to_integer(i);
        invariant 0 <= run_length and run_length <= i;

        initialize by solve();
        preserve by {
            mark iteration;
            let { lo: lo, hi: hi } = unfold(run);
            have hi == i by {
                solve();
            }
            have to_integer(lo + run_length) == to_integer(i) by {
                solve();
            }
            have lo <= i by {
                solve() using {
                    lo <= hi;
                    hi == i;
                };
            }
            have 0 <= i;
            have to_integer(i + 1) <= to_integer(capacity);
            if occupied[i] == 0 {
                have run_length < capacity by {
                    solve() using {
                        run_length <= i;
                        i < capacity;
                    };
                }
                branch {
                    step();
                } else {
                    contradiction(not (occupied[i] == 0));
                }
                step();
                have hi == at(iteration, i) by {
                    solve();
                }
                have to_integer(i) == to_integer(at(iteration, i) + 1) by {
                    normalize();
                }
                have lo <= at(iteration, i) by {
                    solve() using {
                        lo <= hi;
                        hi == at(iteration, i);
                    };
                }
                have to_integer(at(iteration, i)) < to_integer(at(iteration, i) + 1);
                have at(iteration, i) < i by {
                    rewrite(to_integer(i), to_integer(at(iteration, i) + 1));
                    known();
                }
                have at(iteration, i) <= i;
                have lo <= i;
                have i <= capacity by {
                    solve();
                }
                have to_integer(run_length) == to_integer(at(iteration, run_length) + 1) by {
                    normalize();
                }
                have to_integer(lo + at(iteration, run_length)) == to_integer(at(iteration, i)) by {
                    solve();
                }
                have to_integer(lo + run_length) == to_integer(i) by {
                    rewrite(to_integer(run_length), to_integer(at(iteration, run_length) + 1));
                    rewrite(to_integer(i), to_integer(at(iteration, i) + 1));
                    solve();
                }
                have 0 <= run_length and run_length <= i by {
                    solve();
                }
                let run = fold(arena_scan(data, occupied, capacity), {
                    lo: lo, hi: i
                });
                have run.hi == i by {
                    solve();
                }
                have to_integer(run.lo + run_length) == to_integer(i) by {
                    solve();
                }
                have 0 <= at(iteration, i) by {
                    known();
                }
                have 0 <= to_integer(capacity - at(iteration, i) - 1) by {
                    solve() using {
                        0 <= at(iteration, i);
                        at(iteration, i) < at(iteration, capacity);
                        0 <= capacity;
                    };
                }
                have to_integer(capacity - at(iteration, i) - 1)
                    < to_integer(capacity - at(iteration, i)) by {
                    solve() using {
                        0 <= at(iteration, i);
                        at(iteration, i) < at(iteration, capacity);
                        0 <= capacity;
                    };
                }
            } else {
                branch {
                    contradiction(occupied[i] == 0);
                } else {
                    step();
                }
                step();
                have 0 <= i;
                have i <= capacity;
                let run = fold(arena_scan(data, occupied, capacity), {
                    lo: i, hi: i
                });
                have 0 <= at(iteration, i) by {
                    known();
                }
                have 0 <= to_integer(capacity - at(iteration, i) - 1) by {
                    solve() using {
                        0 <= at(iteration, i);
                        at(iteration, i) < at(iteration, capacity);
                        0 <= capacity;
                    };
                }
                have to_integer(capacity - at(iteration, i) - 1)
                    < to_integer(capacity - at(iteration, i)) by {
                    solve() using {
                        0 <= at(iteration, i);
                        at(iteration, i) < at(iteration, capacity);
                        0 <= capacity;
                    };
                }
            }
        }
    }
    let { lo: run_lo, hi: run_hi } = unfold(run);
    fold(arena_cells(data, occupied, capacity));
}
```

```expect
pass
```
