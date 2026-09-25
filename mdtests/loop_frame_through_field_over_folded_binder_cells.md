# Framing cells a folded loop binder owns through a struct field

`mark_run` marks the cells `[start, end)` of an occupancy map reached
through a struct field, `arena->occupied`, in a loop that owns a
field-bearing `window` over the whole map. The window has to own the whole
map whenever its body declares iterated guarded ownership, because a guard
cell must be owned by the body that reads it; the per-cell arena's mark and
clear loops have exactly this shape. The loop never writes a cell below
`start`, and the contract says so: every such cell keeps its entry value.

A loop that declares a resource havocs all memory the resource owns, so the
frame of the untouched cells is a loop invariant,
`forall k in [0, start): arena->occupied[k] == old(arena->occupied[k])`.
Initialization and the per-iteration step check it, the step as a transport
across the one store the body makes, and the back edge closes it with the
binder folded again.

The field `arena->occupied` is owned by the function through
`object(arena)`, outside the loop's havoc, so the loop head copies its cell
back unchanged and every read of it names the one pointer the function
loaded at entry. The back edge's viewability obligation for
`arena->occupied[k]` is stated over that pointer, and the smart closer
discharges it from the entry viewability of the map, spelled through the
field, exactly as it does when the map is a parameter
(`loop_frame_through_parameter_over_folded_binder_cells.md`). Writing the
field inside the loop breaks the frame
(`loop_frame_rejects_rewritten_base_field.md`).

```c filename=loop_old_invariant_through_field_pointer.c
struct arena {
    int32* data;
    int32* occupied;
    int32 capacity;
    int32 live_regions;
};

void mark_run(struct arena* arena, int32 start, int32 end) {
    int32 i;
    arena->occupied[start] = 0;
    i = start;
    while (i < end) {
        arena->occupied[i] = 1;
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

verifying "loop_old_invariant_through_field_pointer.c";

void mark_run(struct arena* arena, int32 start, int32 end) {
    owns object(arena);
    consumes w: window(arena->occupied, arena->capacity, start, end);
    requires separate(
        memory(object(arena)),
        memory(arena->occupied[0..arena->capacity])
    );
    requires w.next == start;
    requires start < end;
    ensures forall (k: int32) {
        0 <= k and k < start implies arena->occupied[k] == old(arena->occupied[k])
    };
} by {
    let { next: n0 } = unfold(w);
    have 0 <= start by simp;
    have start < arena->capacity by simp;
    step();
    step();
    have arena->occupied[start] == 0 by simp;
    step();
    let w = fold(window(arena->occupied, arena->capacity, start, end), { next: start });
    mark pre;
    loop {
        owns w: window(arena->occupied, arena->capacity, start, end);
        invariant w.next == i;
        invariant forall (k: int32) {
            0 <= k and k < start implies arena->occupied[k] == old(arena->occupied[k])
        };
        decreases end - i;
        initialize by {
            have forall (k: int32) {
                0 <= k and k < start implies arena->occupied[k] == old(arena->occupied[k])
            } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k < start);
                transport(
                    old(arena->occupied[k]) == old(arena->occupied[k]),
                    arena->occupied[k] == old(arena->occupied[k])
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
            have i < arena->capacity by {
                apply(int32_lt_le_transitive(i, end, arena->capacity)) using {
                    i < end;
                    end <= arena->capacity;
                }
            }
            mark opened;
            step();
            step();
            have forall (k: int32) {
                start <= k and k < at(opened, i) + 1 implies arena->occupied[k] == 1
            } by {
                intro();
                intro();
                extract(start <= k);
                extract(k < at(opened, i) + 1);
                if k < at(opened, i) {
                    have k < m by simp;
                    have at(opened, arena->occupied[k]) == 1 by {
                        instantiate(forall (j: int32) {
                            at(opened, start) <= at(opened, j) and
                                at(opened, j) < at(opened, m) implies
                                at(opened, arena->occupied[j]) == at(opened, 1)
                        }, k) using {
                            start <= k;
                            k < m;
                        }
                        assumption();
                    }
                    have 0 <= k by simp;
                    transport(at(opened, arena->occupied[k]) == 1, arena->occupied[k] == 1) using {
                        at(opened, arena->occupied[k]) == 1;
                        k < at(opened, i);
                        0 <= k;
                        0 <= at(opened, i);
                        at(opened, i) < arena->capacity;
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
                0 <= k and k < start implies arena->occupied[k] == old(arena->occupied[k])
            } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k < start);
                have at(opened, arena->occupied[k]) == old(arena->occupied[k]) by {
                    instantiate(forall (j: int32) {
                        at(opened, 0) <= at(opened, j) and
                            at(opened, j) < at(opened, start) implies
                            at(opened, arena->occupied[j]) == old(arena->occupied[j])
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
                    at(opened, arena->occupied[k]) == old(arena->occupied[k]),
                    arena->occupied[k] == old(arena->occupied[k])
                ) using {
                    at(opened, arena->occupied[k]) == old(arena->occupied[k]);
                    k < at(opened, i);
                    0 <= k;
                    0 <= at(opened, i);
                    at(opened, i) < arena->capacity;
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
            let w = fold(window(arena->occupied, arena->capacity, start, end), {
                next: at(opened, i) + 1
            });
            have 0 <= end - at(opened, i) - 1 by {
                arithmetic() using {
                    at(opened, i) < end;
                    0 <= at(opened, i);
                    end <= arena->capacity;
                }
            }
            have end - at(opened, i) - 1 < end - at(opened, i) by {
                arithmetic() using {
                    at(opened, i) < end;
                    0 <= at(opened, i);
                    end <= arena->capacity;
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
