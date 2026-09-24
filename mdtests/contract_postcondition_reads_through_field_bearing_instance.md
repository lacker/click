# A postcondition reads a cell a folded field-bearing instance owns

`read` borrows a region instance that owns the descriptor and the data
interval `[start, end)`, and a metadata instance, reached through
`region->arena`, that owns the arena's data pointer. It returns both folded and
states the value it read in C terms,
`result == region->arena->data[region->start + index]`.

Certifying that claim reads three cells at the function's entry and exit, all
inside instances the contract holds folded: `region->arena` and
`region->start` in the region's descriptor, the data pointer in the metadata,
and the data cell in the region's interval. Contract certification reads them
through the cells those instances' unconditional, unmatched bodies own, as
the checked execution did; the index premise `r.start + index < r.end` places
the cell inside the interval. This is the shape of `examples/arena`'s prefix
`arena_read`.

```c filename=read.c
struct arena {
    int32* data;
    int32 live_regions;
};

struct region {
    struct arena* arena;
    int32 start;
    int32 end;
};

int32 read(struct region* region, int32 index) {
    struct arena* arena;

    arena = region->arena;
    return arena->data[region->start + index];
}
```

```click
resource arena_meta(arena: struct arena*) {
    field live: int32;
    owns &arena->data;
    owns arena->live_regions;
}

resource live_region(region: struct region*) {
    field start: int32;
    field end: int32;
    owns object(region);
    owns region->arena->data[start..end];
    fact region->start == start;
    fact region->end == end;
    fact 0 <= start;
    fact start < end;
}

verifying "read.c";

int32 read(struct region* region, int32 index) {
    owns r: live_region(region);
    owns meta: arena_meta(region->arena);
    requires 0 <= index;
    requires defined(r.start + index) and r.start + index < r.end;

    ensures r.start == old(r.start);
    ensures r.end == old(r.end);
    ensures meta.live == old(meta.live);
    ensures result == region->arena->data[region->start + index];
} by {
    let { live: n } = unfold(meta);
    let { start: s, end: e } = unfold(r);
    have defined(s + index) by {
        simp() using {
            defined(s + index) and s + index < e;
        }
    }
    have s + index < e by {
        simp() using {
            defined(s + index) and s + index < e;
        }
    }
    have s <= s + index by {
        apply(int32_add_nonnegative_right_is_at_least_left(s, index)) using {
            0 <= index;
            defined(s + index);
        }
    }
    have s + index + 1 <= e by {
        apply(int32_increment_upper_bound(s + index, e)) using {
            s + index < e;
        }
    }
    have region->start == s by {
        assumption();
    }
    have defined(region->start + index) by {
        rewrite(region->start == s);
        assumption();
    }
    have region->start <= region->start + index by {
        rewrite(region->start == s);
        assumption();
    }
    have region->start + index + 1 <= e by {
        rewrite(region->start == s);
        assumption();
    }
    execute();
    let r = fold(live_region(region), { start: s, end: e });
    let meta = fold(arena_meta(region->arena), { live: n });
    simp();
}
```

```expect
pass
```
