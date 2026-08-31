resource arena_region(region: struct region*) {
    owns object(region);
    views region->arena->data;
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
