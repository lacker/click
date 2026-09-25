# Framing cells a folded loop binder owns through a parameter

The control for `loop_frame_through_field_over_folded_binder_cells.md`: the
same `mark_run`, loop, window, and proof, with the occupancy map passed as a
parameter `int32* occupied` instead of read through `arena->occupied`. The
map's base is then a parameter value rather than a load, so the frame
invariant `forall k in [0, start): occupied[k] == old(occupied[k])` closes at
the back edge without any reasoning about the base: the viewability of
`occupied[k]` comes from the entry viewability of the map, and the equality
from the per-iteration transport the body proves. The field form must close
the same way.

```c filename=loop_frame_through_parameter.c
void mark_run(int32* occupied, int32 capacity, int32 start, int32 end) {
    int32 i;
    occupied[start] = 0;
    i = start;
    while (i < end) {
        occupied[i] = 1;
        i = i + 1;
    }
}
```

```click
resource window(occupied: int32*, capacity: int32, start: int32, end: int32) {
    field next: int32;
    owns occupied[0..capacity];
    fact 0 <= start;
    fact start <= next;
    fact next <= end;
    fact end <= capacity;
    fact forall (k: int32) {
        start <= k and k < next implies occupied[k] == 1
    };
}

verifying "loop_frame_through_parameter.c";

void mark_run(int32* occupied, int32 capacity, int32 start, int32 end) {
    consumes w: window(occupied, capacity, start, end);
    requires w.next == start;
    requires start < end;
    ensures forall (k: int32) {
        0 <= k and k < start implies occupied[k] == old(occupied[k])
    };
} by {
    let { next: n0 } = unfold(w);
    have 0 <= start by simp;
    have start < capacity by simp;
    step();
    step();
    have occupied[start] == 0 by simp;
    step();
    let w = fold(window(occupied, capacity, start, end), { next: start });
    mark pre;
    loop {
        owns w: window(occupied, capacity, start, end);
        invariant w.next == i;
        invariant forall (k: int32) {
            0 <= k and k < start implies occupied[k] == old(occupied[k])
        };
        decreases end - i;
        initialize by {
            have forall (k: int32) {
                0 <= k and k < start implies occupied[k] == old(occupied[k])
            } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k < start);
                transport(
                    old(occupied[k]) == old(occupied[k]),
                    occupied[k] == old(occupied[k])
                ) using {
                    0 <= k;
                    k < start;
                }
            }
            simp();
        }
        preserve by {
            let { next: m } = unfold(w);
            have m == i by simp;
            have i < end by simp;
            have start <= m by simp;
            have 0 <= m by {
                apply(int32_le_transitive(0, start, m)) using {
                    0 <= start;
                    start <= m;
                }
            }
            have 0 <= i by {
                rewrite(i == m);
                assumption();
            }
            have i < capacity by {
                apply(int32_lt_le_transitive(i, end, capacity)) using {
                    i < end;
                    end <= capacity;
                }
            }
            mark opened;
            step();
            step();
            have forall (k: int32) {
                start <= k and k < at(opened, i) + 1 implies occupied[k] == 1
            } by {
                intro();
                intro();
                extract(start <= k);
                extract(k < at(opened, i) + 1);
                if k < at(opened, i) {
                    have k < m by simp;
                    have at(opened, occupied[k]) == 1 by {
                        instantiate(forall (j: int32) {
                            at(opened, start) <= at(opened, j) and
                                at(opened, j) < at(opened, m) implies
                                at(opened, occupied[j]) == at(opened, 1)
                        }, k) using {
                            start <= k;
                            k < m;
                        }
                        assumption();
                    }
                    have 0 <= k by simp;
                    transport(at(opened, occupied[k]) == 1, occupied[k] == 1) using {
                        at(opened, occupied[k]) == 1;
                        k < at(opened, i);
                        0 <= k;
                        0 <= at(opened, i);
                        at(opened, i) < capacity;
                    }
                } else {
                    have k <= at(opened, i) by {
                        apply(int32_lt_successor_implies_le(k, at(opened, i))) using {
                            k < at(opened, i) + 1;
                        }
                    }
                    have k == at(opened, i) by {
                        apply(int32_le_and_not_lt_implies_eq(k, at(opened, i))) using {
                            k <= at(opened, i);
                            not (k < at(opened, i));
                        }
                    }
                    rewrite(k == at(opened, i));
                    normalize();
                }
            }
            have start <= at(opened, i) by {
                rewrite(at(opened, i) == m);
                assumption();
            }
            have forall (k: int32) {
                0 <= k and k < start implies occupied[k] == old(occupied[k])
            } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k < start);
                have at(opened, occupied[k]) == old(occupied[k]) by {
                    instantiate(forall (j: int32) {
                        at(opened, 0) <= at(opened, j) and
                            at(opened, j) < at(opened, start) implies
                            at(opened, occupied[j]) == old(occupied[j])
                    }, k) using {
                        0 <= k;
                        k < start;
                    }
                    assumption();
                }
                have k < at(opened, i) by {
                    apply(int32_lt_le_transitive(k, start, at(opened, i))) using {
                        k < start;
                        start <= at(opened, i);
                    }
                }
                transport(
                    at(opened, occupied[k]) == old(occupied[k]),
                    occupied[k] == old(occupied[k])
                ) using {
                    at(opened, occupied[k]) == old(occupied[k]);
                    k < at(opened, i);
                    0 <= k;
                    0 <= at(opened, i);
                    at(opened, i) < capacity;
                }
            }
            have start <= at(opened, i) + 1 by {
                apply(int32_increment_lower_bound(at(opened, i), start, end)) using {
                    start <= at(opened, i);
                    at(opened, i) < end;
                }
            }
            have at(opened, i) + 1 <= end by {
                apply(int32_increment_upper_bound(at(opened, i), end)) using {
                    at(opened, i) < end;
                }
            }
            let w = fold(window(occupied, capacity, start, end), {
                next: at(opened, i) + 1
            });
            have 0 <= end - at(opened, i) - 1 by {
                arithmetic() using {
                    at(opened, i) < end;
                    0 <= at(opened, i);
                    end <= capacity;
                }
            }
            have end - at(opened, i) - 1 < end - at(opened, i) by {
                arithmetic() using {
                    at(opened, i) < end;
                    0 <= at(opened, i);
                    end <= capacity;
                }
            }
            close_invariants();
        }
    }
    let { next: n } = unfold(w);
    execute();
    simp();
}
```

```expect
pass
```
