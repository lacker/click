# region-relative indexed read

A composite region owns `[start, end)` of its backing array. A nonnegative
relative index whose translated absolute index is below `end` must authorize
the corresponding one-cell read in both proof planning and kernel
certification.

```c filename=region_read.c
struct region {
    int32* data;
    int32 start;
    int32 end;
};

int32 region_read(struct region* region, int32 index) {
    return region->data[region->start + index];
}
```

```click
resource live_region(region: struct region*) {
    owns object(region);
    owns region->data[region->start..region->end];
}

verifying "region_read.c";

int32 region_read(struct region* region, int32 index) {
    requires 0 <= index;
    requires defined(region->start + index) and
        region->start + index < region->end;
    views live_region(region);
    immutable;
    ensures result == region->data[region->start + index];
} by {
    unfold(live_region(region));
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
    step();
    frame();
    simp();
}
```

```expect
pass
```
