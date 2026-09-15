resource arena_metadata(arena: struct arena*) {
    owns arena->data;
    owns arena->occupied;
    owns arena->capacity;
    owns arena->live_regions;
    contains allocation(arena->data, arena->capacity * 4);
    contains allocation(arena->occupied, arena->capacity * 4);
    fact 0 <= arena->capacity;
    fact arena->capacity <= 536870911;
    fact separate(
        memory(object(arena)),
        memory(arena->data[0..arena->capacity])
    );
    fact separate(
        memory(object(arena)),
        memory(arena->occupied[0..arena->capacity])
    );
}

resource arena_region(region: struct region*) {
    owns object(region);
    contains arena_metadata(region->arena);
    owns region->arena->data[region->start..region->end];
    owns region->arena->occupied[region->start..region->end];
}

resource arena_available(region: struct region*) {
    owns region->arena->data[region->start..region->end];
    owns region->arena->occupied[region->start..region->end];
}

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

resource arena_empty(arena: struct arena*) {
    owns object(arena);
    contains arena_initialized_storage(
        arena->data,
        arena->occupied,
        arena->capacity,
        1
    );
    contains arena_initialized_access(
        arena->data,
        arena->occupied,
        arena->capacity,
        1
    );
    fact arena->live_regions == 0;
}

verifying "arena_init.c";
verifying "arena_alloc.c";
verifying "arena_region_length.c";
verifying "arena_read.c";
verifying "arena_write.c";
verifying "arena_free.c";
verifying "arena_destroy.c";
verifying "arena_pipeline.c";

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
        invariant 0 <= i and i <= capacity;
        invariant forall (k: int32) {
            0 <= k and k < i implies occupied[k] == 0
        };
        owns occupied[0..capacity];

        initialize by simp;
        preserve by {
            step();
            step();
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

int32 arena_region_length(struct region* region) {
    requires 0 <= region->start;
    requires region->start <= region->end;
    views arena_region(region);

    ensures result == region->end - region->start;
} by {
    open(arena_region(region)) {
        have defined(region->end - region->start) by {
            apply(int32_nonnegative_subtract_within_value_is_defined(
                region->end,
                region->start
            )) using {
                0 <= region->start;
                region->start <= region->end;
            }
        }
        step();
        simp();
    }
}

int32 arena_read(struct region* region, int32 index) {
    requires 0 <= index;
    requires defined(region->start + index) and
        region->start + index < region->end;
    views arena_region(region);

    ensures result == region->arena->data[region->start + index];
} by {
    have defined(region->start + index) by {
        simp() using {
            defined(region->start + index) and
                region->start + index < region->end;
        }
    }
    have region->start + index < region->end by {
        simp() using {
            defined(region->start + index) and
                region->start + index < region->end;
        }
    }
    have 0 <= index by {
        assumption();
    }
    have region->start <= region->start + index by {
        apply(int32_add_nonnegative_right_is_at_least_left(
            region->start,
            index
        )) using {
            0 <= index;
            defined(region->start + index);
        }
    }
    have region->start + index + 1 <= region->end by {
        apply(int32_increment_upper_bound(
            region->start + index,
            region->end
        )) using {
            region->start + index < region->end;
        }
    }
    observe(arena_region(region));
    observe(arena_metadata(region->arena));
    open(arena_region(region)) {
        open(arena_metadata(region->arena)) {
            step();
            step();
            step();
            simp();
        }
    }
}

void arena_write(struct region* region, int32 index, int32 value) {
    requires 0 <= index;
    requires defined(region->start + index) and
        region->start + index < region->end;
    owns arena_region(region);

    ensures region->arena->data[region->start + index] == value;
} by {
    observe(arena_region(region));
    observe(arena_metadata(region->arena));
    open(arena_region(region)) {
        open(arena_metadata(region->arena)) {
            have defined(region->start + index) by {
                simp() using {
                    defined(region->start + index) and
                        region->start + index < region->end;
                }
            }
            have region->start + index < region->end by {
                simp() using {
                    defined(region->start + index) and
                        region->start + index < region->end;
                }
            }
            have 0 <= index by {
                assumption();
            }
            have region->start <= region->start + index by {
                apply(int32_add_nonnegative_right_is_at_least_left(
                    region->start,
                    index
                )) using {
                    0 <= index;
                    defined(region->start + index);
                }
            }
            have region->start + index + 1 <= region->end by {
                apply(int32_increment_upper_bound(
                    region->start + index,
                    region->end
                )) using {
                    region->start + index < region->end;
                }
            }
            execute();
            simp();
        }
    }
}

void arena_free(struct region* region) {
    requires 0 <= region->start;
    requires region->start <= region->end;
    requires region->end <= region->arena->capacity;
    requires 1 <= region->arena->live_regions;
    consumes arena_region(region);
    produces object(region);
    produces arena_metadata(region->arena);
    produces arena_available(region);
} by {
    unfold(arena_region(region));
    unfold(arena_metadata(region->arena));
    step();
    step();
    step();
    step();
    loop as clear_occupied {
        invariant region->start <= i and i <= region->end;
        owns region->arena->occupied[region->start..region->end];
        initialize by {
            have region->start <= i and i <= region->end by {
                have i == region->start by {
                    normalize();
                }
                have region->start <= i by {
                    rewrite(i == region->start);
                    normalize();
                }
                have i <= region->end by {
                    rewrite(i == region->start);
                    assumption();
                }
                split();
            }
        }
        preserve by {
            have i < region->end by {
                assumption();
            }
            have i < region->arena->capacity by {
                apply(int32_lt_le_transitive(
                    i,
                    region->end,
                    region->arena->capacity
                )) using {
                    i < region->end;
                    region->end <= region->arena->capacity;
                }
                assumption();
            }
            have region->arena->capacity < 2147483647 by {
                apply(int32_le_lt_transitive(
                    region->arena->capacity,
                    536870911,
                    2147483647
                )) using {
                    region->arena->capacity <= 536870911;
                }
                assumption();
            }
            have i < 2147483647 by {
                apply(int32_lt_transitive(
                    i,
                    region->arena->capacity,
                    2147483647
                )) using {
                    i < region->arena->capacity;
                    region->arena->capacity < 2147483647;
                }
                assumption();
            }
            step();
            step();
            have region->start <= i by {
                simp();
            }
            have i <= region->end by {
                simp();
            }
            close_invariants();
        }
    }
    step();
    step();
    fold(arena_available(region));
    fold(arena_metadata(region->arena));
    simp();
}

void arena_destroy(struct arena* arena) {
    consumes arena_empty(arena);
    produces object(arena);

    ensures arena->data == 0;
    ensures arena->occupied == 0;
    ensures arena->capacity == 0;
    ensures arena->live_regions == 0;
} by {
    unfold(arena_empty(arena));
    unfold(arena_initialized_storage(
        arena->data,
        arena->occupied,
        arena->capacity,
        1
    ));
    unfold(arena_initialized_access(
        arena->data,
        arena->occupied,
        arena->capacity,
        1
    ));
    execute();
    simp();
}
