# A post-return fold retains the readability of a stored cell

Reduced from `arena_write`: the symbolic store materializes one cell within
a larger owned interval. Its exact-width read validity is intrinsic to that
memory state. A post-return quantified proof followed by resource folds
must not lose that fact during certification. The C is the unchanged arena
write function.

```c filename=arena_write.c
struct arena {
    int32* data;
    int32* occupied;
    int32 capacity;
    int32 live_regions;
};

struct region {
    struct arena* arena;
    int32 start;
    int32 end;
};

void arena_write(struct region* region, int32 index, int32 value) {
    struct arena* arena;

    arena = region->arena;
    arena->data[region->start + index] = value;
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
        owns allocation(data, capacity * 4);
        owns allocation(occupied, capacity * 4);
        fact 1 <= capacity;
        fact capacity <= 536870911;
    }
}

resource arena_cells(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
}

resource arena_state(arena: struct arena*) {
    field live: int32;
    field capacity: int32;
    owns arena->data;
    owns arena->occupied;
    owns arena->capacity;
    owns arena->live_regions;
    owns arena_initialized_storage(
        arena->data,
        arena->occupied,
        arena->capacity,
        1
    );
    owns arena_cells(arena->data, arena->occupied, arena->capacity);
    fact arena->capacity <= 536870911;
    fact arena->capacity == capacity;
    fact arena->live_regions == live;
    fact 0 <= live;
    fact separate(
        memory(arena->occupied[0..arena->capacity]),
        memory(arena->data[0..arena->capacity])
    );
    fact separate(
        memory(*arena),
        memory(arena->data[0..arena->capacity])
    );
    fact separate(
        memory(*arena),
        memory(arena->occupied[0..arena->capacity])
    );
}

resource arena_region(region: struct region*) {
    field start: int32;
    field end: int32;
    owns *region;
    owns region->arena->data[start..end];
    fact region->start == start;
    fact region->end == end;
    fact 0 <= start;
    fact start < end;
}

verifying "arena_write.c";

void arena_write(struct region* region, int32 index, int32 value) {
    owns r: arena_region(region);
    owns st: arena_state(old(region->arena));
    requires 0 <= index;
    requires defined(r.start + index) and to_integer(r.start + index) < to_integer(r.end);
    requires r.end <= st.capacity;

    ensures r.start == old(r.start);
    ensures r.end == old(r.end);
    ensures st.capacity == old(st.capacity);
    ensures r.end <= st.capacity;
    ensures st.live == old(st.live);
    ensures region->arena == old(region->arena);
    ensures region->arena->capacity == old(region->arena->capacity);
    ensures region->arena->data == old(region->arena->data);
    ensures region->arena->data[region->start + index] == value;
    ensures region->arena->data[r.start + index] == value;
    ensures forall (k: int32) {
        0 <= k and k < region->arena->capacity implies
            region->arena->occupied[k] == old(region->arena->occupied[k])
    };
} by {
    let { live: n, capacity: c } = unfold(st);
    let { start: s, end: e } = unfold(r);
    have defined(s + index) by {
        solve() using {
            defined(s + index) and to_integer(s + index) < to_integer(e);
        };
    }
    have to_integer(s + index) < to_integer(e) by {
        solve() using {
            defined(s + index) and to_integer(s + index) < to_integer(e);
        };
    }
    have to_integer(s) <= to_integer(s + index);
    have to_integer(s + index + 1) <= to_integer(e);
    have region->start == s by {
        known();
    }
    have defined(region->start + index) by {
        rewrite(region->start, s);
        known();
    }
    have to_integer(region->start) <= to_integer(region->start + index) by {
        rewrite(region->start, s);
        known();
    }
    have defined(s + index + 1);
    have defined(region->start + index + 1) by {
        rewrite(region->start, s);
        known();
    }
    have to_integer(region->start + index + 1) <= to_integer(e) by {
        rewrite(region->start, s);
        known();
    }
    have 0 <= to_integer(region->start + index) by {
        rewrite(region->start, s);
        have 0 <= to_integer(s + index);
        known();
    }
    have to_integer(s + index) < to_integer(c);
    have region->arena->capacity == c by {
        solve();
    }
    have to_integer(region->start + index) < to_integer(region->arena->capacity) by {
        rewrite(region->start, s);
        rewrite(region->arena->capacity, c);
        known();
    }
    mark w;
    step_until(function.exit);
    have forall (k: int32) {
        0 <= k and k < at(w, region->arena->capacity) implies
            at(w, region->arena->occupied[k]) == region->arena->occupied[k]
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < at(w, region->arena->capacity));
        solve();
    }
    let r = fold(arena_region(region), { start: s, end: e });
    let st = fold(arena_state(region->arena), { live: n, capacity: c });
    solve();
}

```
```expect
pass
```
