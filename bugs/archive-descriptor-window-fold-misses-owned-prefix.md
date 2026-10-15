# Archived descriptor-window fold misses an owned prefix

Priority: P2.

Soundness: not soundness. The archived object-model implementation rejects a
valid range reassembly. This reproduction does not demonstrate false acceptance.

The violated invariant is that ownership of adjacent fragments can reassemble
one resource body when checked reads prove their bases denote the same address.
Selecting a descriptor field must preserve that behavior across the loop.

## Reproduction

At recovery checkpoint `31c252a80`, save these blocks as `probe.c` and
`probe.click`, then run `click verify probe.click`. The proof stops at the
`arena_window` fold with `fold requires ownership of the complete instance body`.
The C preserves the original arena's direct descriptor-field accesses and
occupancy update. It has no proof-only locals or source rewrites.

```c
struct arena { int32* data; int32* occupied; int32 capacity; };
void claim_run(struct arena* arena, int32 start, int32 end) {
    int32 i;
    i = start;
    while (i < end) {
        arena->occupied[i] = 1;
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

verifying "probe.c";

void claim_run(struct arena* arena, int32 start, int32 end) {
    views arena->data;
    views arena->occupied;
    views arena->capacity;

    consumes w: arena_window(arena->data, arena->occupied, arena->capacity, start, end);
    requires w.next == start;
    produces arena_cells(arena->data, arena->occupied, arena->capacity);
    produces region(arena->data, start, end);
} by {
    step();
    step();
    loop {
        owns w: arena_window(arena->data, arena->occupied, arena->capacity, start, end);
        invariant w.next == i;
        decreases end - i;

        initialize by simp;
        preserve by {
            let { next: n } = unfold(w);
            have n == i;
            have n <= i;
            have i < end;
            have end <= arena->capacity;
            have forall (k: int32) {
                i + 1 <= k and k < end implies arena->occupied[k] == 0
            } by {
                intro();
                intro();
                extract(i + 1 <= k);
                apply(int32_increment_strictly_increases(i, end)) using {
                    i < end;
                }
                apply(int32_increment_less_equal_implies_less_than(i, k)) using {
                    i < i + 1;
                    i + 1 <= k;
                }
                apply(int32_less_than_implies_less_equal(i, k)) using {
                    i < k;
                }
                have n <= k by {
                    rewrite(n == i);
                    assumption();
                }
                instantiate(forall (k: int32) {
                    n <= k and k < end implies arena->occupied[k] == 0
                }, k) using {
                    n <= k;
                    k < end;
                }
                assumption();
            }
            have arena->occupied[i] == 0 by {
                instantiate(forall (k: int32) {
                    n <= k and k < end implies arena->occupied[k] == 0
                }, i) using {
                    n <= i;
                    i < end;
                }
                assumption();
            }
            take(arena->data[i..i + 1]);
            have start <= i;
            have 0 <= i;
            have i < arena->capacity;
            mark opened;
            step();
            have forall (k: int32) {
                at(opened, i) + 1 <= k and k < end implies arena->occupied[k] == 0
            } by {
                intro();
                intro();
                extract(at(opened, i) + 1 <= k);
                have at(opened, arena->occupied[k]) == 0 by {
                    instantiate(forall (k: int32) {
                        at(opened, i) + 1 <= k and k < end implies at(opened, arena->occupied[k]) == 0
                    }, k) using {
                        at(opened, i) + 1 <= k;
                        k < end;
                    }
                    assumption();
                }
                have at(opened, i) < end;
                apply(int32_increment_strictly_increases(at(opened, i), end)) using {
                    at(opened, i) < end;
                }
                apply(int32_increment_less_equal_implies_less_than(at(opened, i), k)) using {
                    at(opened, i) < at(opened, i) + 1;
                    at(opened, i) + 1 <= k;
                }
                have 0 <= at(opened, i) by assumption();
                have at(opened, i) < arena->capacity by assumption();
                have 0 <= k;
                have k < arena->capacity;
                transport(
                    at(opened, arena->occupied[k]) == 0,
                    arena->occupied[k] == 0
                ) using {
                    at(opened, arena->occupied[k]) == 0;
                    at(opened, i) < k;
                    0 <= at(opened, i);
                    at(opened, i) < arena->capacity;
                    0 <= k;
                    k < arena->capacity;
                    separate(memory(arena->occupied[0..arena->capacity]), memory(arena->data[0..arena->capacity]));
                }
                assumption();
            }
            step();
            let w = fold(arena_window(arena->data, arena->occupied, arena->capacity, start, end), {
                next: at(opened, i) + 1
            });
            have 0 <= end - at(statement(3).entry, i) - 1 by {
                arithmetic() using {
                    at(statement(3).entry, i) < end;
                    0 <= at(statement(3).entry, i);
                    end <= arena->capacity;
                }
            }
            have end - at(statement(3).entry, i) - 1 < end - at(statement(3).entry, i) by {
                arithmetic() using {
                    at(statement(3).entry, i) < end;
                    0 <= at(statement(3).entry, i);
                    end <= arena->capacity;
                }
            }
            close_invariants();
        }
    }
    let { next: n } = unfold(w);
    execute();
    fold(arena_cells(arena->data, arena->occupied, arena->capacity));
    fold(region(arena->data, start, end));
    simp();
}
```

The same C and proof verify on upstream-based `64f0f0d46` after prepending
`import click::machine_integer;`, required by upstream's library-module migration.
The raw-pointer version in `mdtests/iterated_ownership_claim_loop.md` is the
starting reduction; this case retains the descriptor selectors that distinguish
it from that control.

## Evidence and acceptance criteria

A temporary probe at range consumption finds two same-address owned fragments:
one starts at the requested start, and one ends at the requested end. Only the
suffix is selected by the resource index. Neither selected occurrence has a loan
dependency or supported-view binding, so the join is refused for having only one
supplier. Checked memory-read equality recognizes both bases. Reusing upstream
`a676ba284`'s held-owner separation repair does not resolve this selection miss.

Restore fresh, expanded, rewritten and retained checking of this unchanged
program and its original contracts. Keep candidate discovery indexed; do not
scan unrelated resources or publish scoped read equality into a weaker context.
Retain wrong-slot, overwritten-field, missing-descriptor-view and physical-width
rejection controls, and deterministic tests with growing unrelated state. The
original `examples/arena/arena_cells.click` must pass its window fold as well.
