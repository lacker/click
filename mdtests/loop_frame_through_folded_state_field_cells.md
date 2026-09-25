# Framing a map read through a field a folded state resource owns

`mark_run` is `loop_frame_through_field_over_folded_binder_cells.md` with the
arena's fields owned by a field-bearing `state` resource instead of the
function's own `object(arena)`, the shape `examples/arena`'s `arena_state`
has. The proof unfolds the state before it executes, so the fields
`&arena->occupied` and `arena->capacity` are held outright, outside the
loop's havoc, and the loop that owns the `window` over the map keeps
`forall k in [0, start): arena->occupied[k] == old(arena->occupied[k])`.

Unfolding the state names each field cell at its folded value, and a
pointer field is named as the word that carries its load variable, which is
what the C evaluator returns as the loaded pointer. The invariant lowering
used to ask for the field cell's viewability anyway, because the word is
narrower than the pointer the lowering reads, and lowering at a loop head
defers every viewability that is not an exact fact. The back-edge bundle then
carried four members, a field member and a map member at the back edge and at
the function entry, and the field members had no source spelling: the smart
closer ran out and an explicit closer could not name the cell. The
materialized word is now the load it names, so the field members are gone,
and the frame closes exactly as it does when the function owns the object.

The window is unfolded before the state, at the function entry itself: that
is where the unfold's viewability of the map is recorded, which is the
premise the closer transports to both map members. Unfolding the state first
names its field cells in a new snapshot with no source spelling, and a fact
recorded there cannot be cited
(`loop_frame_at_loop_entry_through_folded_state.md` frames against the loop
entry instead, where the proof states the premise itself).

```c filename=loop_frame_folded_state_fields.c
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

resource state(arena: struct arena*) {
    field capacity: int32;
    owns &arena->data;
    owns &arena->occupied;
    owns arena->capacity;
    owns arena->live_regions;
    fact arena->capacity == capacity;
    fact separate(
        memory(object(arena)),
        memory(arena->occupied[0..arena->capacity])
    );
}

verifying "loop_frame_folded_state_fields.c";

void mark_run(struct arena* arena, int32 start, int32 end) {
    owns st: state(arena);
    consumes w: window(arena->occupied, arena->capacity, start, end);
    requires w.next == start;
    requires start < end;
    ensures forall (k: int32) {
        0 <= k and k < start implies arena->occupied[k] == old(arena->occupied[k])
    };
} by {
    let { next: n0 } = unfold(w);
    let { capacity: c } = unfold(st);
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
    let st = fold(state(arena), { capacity: c });
    simp();
}
```

```expect
pass
```
