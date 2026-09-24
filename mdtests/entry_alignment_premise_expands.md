# An entry alignment fact cited after a loop expands in its source spelling

This is `arena_init` from `examples/arena`, its C unchanged, with only the
resources its own contract names. `consumes object(arena)` gives the
function-entry fact `aligned(arena, 8)`. Expanding the `simp()` that closes
the loop's `preserve` proof cites that fact as a premise read at function
entry.

The fact is `address(arena) & 7u64 == 0u64` inside, and the expansion wrote
it with each side read at entry, as
`at(function.entry, (((uint64)arena) & 7u64)) == at(function.entry, 0u64)`.
Click has no cast spelling for a pointer's address, so the rewrite did not
parse and `click audit examples/arena` failed at that site while
`click verify` accepted the proof. A snapshot-read alignment fact now renders
as `at(function.entry, aligned(arena, 8))`. The loop also follows a
proof-level `branch`, the shape `loop_after_proof_branch_expands.md` reduces.
The expansion regression in `src/surface/tests/expansion_tests.rs` expands
the site and re-verifies the rewrite, and the audit regression in
`src/bin/click-audit/tests.rs` audits every smart site of this file.

```c filename=arena_init.c
struct arena {
    int32* data;
    int32* occupied;
    int32 capacity;
    int32 live_regions;
};

int32 arena_init(struct arena* arena, int32 capacity) {
    int32* data;
    int32* occupied;
    int32 i;

    arena->data = 0;
    arena->occupied = 0;
    arena->capacity = 0;
    arena->live_regions = 0;

    if (capacity <= 0) {
        return 0;
    }
    if (capacity > 536870911) {
        return 0;
    }

    data = malloc(capacity * 4);
    if (data == 0) {
        return 0;
    }

    occupied = malloc(capacity * 4);
    if (occupied == 0) {
        free(data);
        return 0;
    }

    i = 0;
    while (i < capacity) {
        occupied[i] = 0;
        i = i + 1;
    }

    arena->data = data;
    arena->occupied = occupied;
    arena->capacity = capacity;
    return 1;
}
```

```click
resource arena_initialized_storage(
    data: int32*,
    occupied: int32*,
    capacity: int32,
    initialized: int32
) {
    if initialized == 1 {
        contains allocation(data, capacity * 4);
        contains allocation(occupied, capacity * 4);
        fact 1 <= capacity;
        fact capacity <= 536870911;
    }
}

resource arena_initialized_access(
    data: int32*,
    occupied: int32*,
    capacity: int32,
    initialized: int32
) {
    if initialized == 1 {
        owns data[0..capacity];
        owns occupied[0..capacity];
    }
}

resource arena_init_result(arena: struct arena*, initialized: int32) {
    owns object(arena);
    contains arena_initialized_storage(
        arena->data,
        arena->occupied,
        arena->capacity,
        initialized
    );
    fact initialized == 0 or initialized == 1;
    fact initialized == 0 implies arena->data == 0;
    fact initialized == 0 implies arena->occupied == 0;
    fact initialized == 0 implies arena->capacity == 0;
    fact initialized == 0 implies arena->live_regions == 0;
    fact initialized == 1 implies arena->live_regions == 0;
}


verifying "arena_init.c";

int32 arena_init(struct arena* arena, int32 capacity) {
    consumes object(arena);
    produces arena_init_result(arena, result);
    produces arena_initialized_access(
        arena->data,
        arena->occupied,
        arena->capacity,
        result
    );

    ensures result == 0 or result == 1;
    ensures forall (k: int32) {
        result == 1 and 0 <= k and k < arena->capacity implies
            arena->occupied[k] == 0
    };
} by {
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    branch {
        then {
            step();
            fold(arena_initialized_storage(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_initialized_access(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_init_result(arena, result));
            simp();
        }
        else {}
    }
    branch {
        then {
            step();
            fold(arena_initialized_storage(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_initialized_access(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_init_result(arena, result));
            simp();
        }
        else {}
    }
    step();
    branch {
        then {
            step();
            fold(arena_initialized_storage(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_initialized_access(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_init_result(arena, result));
            simp();
        }
        else {}
    }
    step();
    branch {
        then {
            step();
            step();
            fold(arena_initialized_storage(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_initialized_access(
                arena->data,
                arena->occupied,
                arena->capacity,
                result
            ));
            fold(arena_init_result(arena, result));
            simp();
        }
        else {}
    }
    have 1 <= capacity by {
        arithmetic() using {
            not (capacity <= 0);
        }
    }
    have capacity <= 536870911 by {
        arithmetic() using {
            not (capacity > 536870911);
        }
    }
    step();
    loop as initialize_occupied {
        decreases capacity - i;
        invariant 0 <= i and i <= capacity;
        invariant forall (k: int32) {
            0 <= k and k < i implies occupied[k] == 0
        };
        owns occupied[0..capacity];

        initialize by simp;
        preserve by {
            mark iteration;
            step();
            step();
            have 0 <= capacity - at(iteration, i) - 1 by {
                arithmetic() using {
                    0 <= at(iteration, i);
                    at(iteration, i) < capacity;
                    1 <= capacity;
                    capacity <= 536870911;
                }
            }
            have capacity - at(iteration, i) - 1 < capacity - at(iteration, i) by {
                arithmetic() using {
                    0 <= at(iteration, i);
                    at(iteration, i) < capacity;
                    1 <= capacity;
                    capacity <= 536870911;
                }
            }
            simp();
        }
    }
    have i == capacity by {
        apply(int32_le_and_not_lt_implies_eq(i, capacity)) using {
            i <= capacity;
            not (i < capacity);
        }
        assumption();
    }
    have forall (k: int32) {
        0 <= k and k < capacity implies occupied[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < capacity);
        instantiate(forall (j: int32) {
            0 <= j and j < i implies occupied[j] == 0
        }, k) using {
            0 <= k;
            k < capacity;
            i == capacity;
        }
        assumption();
    }
    step();
    step();
    step();
    have forall (k: int32) {
        0 <= k and k < arena->capacity implies arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < arena->capacity);
        have k < capacity by {
            assumption();
        }
        instantiate(forall (j: int32) {
            0 <= j and j < capacity implies occupied[j] == 0
        }, k) using {
            0 <= k;
            k < capacity;
        }
        assumption();
    }
    step();
    have result == 1 by {
        normalize();
    }
    have result == 0 or result == 1 by {
        right();
    }
    have forall (k: int32) {
        result == 1 and 0 <= k and k < arena->capacity implies
            arena->occupied[k] == 0
    } by {
        intro();
        intro();
        extract(result == 1);
        extract(0 <= k);
        extract(k < arena->capacity);
        instantiate(forall (j: int32) {
            0 <= j and j < arena->capacity implies arena->occupied[j] == 0
        }, k) using {
            0 <= k;
            k < arena->capacity;
        }
        assumption();
    }
    fold(arena_initialized_storage(
        arena->data,
        arena->occupied,
        arena->capacity,
        result
    ));
    fold(arena_initialized_access(
        arena->data,
        arena->occupied,
        arena->capacity,
        result
    ));
    fold(arena_init_result(arena, result));
    assumption();
    assumption();
    assumption();
    assumption();
}

```

```expect
pass
```
