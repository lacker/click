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

verifying "arena_init.c";
verifying "arena_alloc.c";
verifying "arena_region_length.c";
verifying "arena_read.c";
verifying "arena_write.c";
verifying "arena_free.c";
verifying "arena_destroy.c";
verifying "arena_pipeline.c";

int32 arena_region_length(struct region* region) {
    requires 0 <= region->start;
    requires region->start <= region->end;
    views arena_region(region);
    immutable;

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
        frame();
        simp();
    }
}

int32 arena_read(struct region* region, int32 index) {
    requires 0 <= index;
    requires defined(region->start + index) and
        region->start + index < region->end;
    views arena_region(region);
    immutable;

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
            frame();
            simp();
        }
    }
}

void arena_write(struct region* region, int32 index, int32 value) {
    requires 0 <= index;
    requires defined(region->start + index) and
        region->start + index < region->end;
    owns arena_region(region);
    mutable region->arena->data[region->start + index..region->start + index + 1];

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
            frame();
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
    mutable region->arena->occupied[region->start..region->end],
        region->arena->live_regions;
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
        mutable region->arena->occupied[region->start..region->end] by frame;
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
    frame();
    simp();
}
