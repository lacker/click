resource arena_metadata(arena: struct arena*) {
    owns arena->data;
    owns arena->capacity;
    contains allocation(arena->data, arena->capacity * 4);
    fact 0 <= arena->capacity;
    fact arena->capacity <= 536870911;
    fact separate(
        memory(object(arena)),
        memory(arena->data[0..arena->capacity])
    );
}

resource arena_region(region: struct region*) {
    owns object(region);
    contains arena_metadata(region->arena);
    owns region->arena->data[region->start..region->end];
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
