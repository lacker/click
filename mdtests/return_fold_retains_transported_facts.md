# Returned pointer-field transports keep their checked proofs

Explicit transports establish unchanged descriptor fields. A selected separation
proof consumes them before a resource fold. Retain those transport derivations
and the scope's original assumptions, including when its checked premise
selection derives the requested separation. The C is the original arena write.

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
resource arena_cells(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];

}

resource arena_state(arena: struct arena*) {
    field live: int32;
    field capacity: int32;
    owns arena->data;
    owns arena->occupied;
    owns arena->capacity;
    owns arena->live_regions;
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
    requires defined(r.start + index) and r.start + index < r.end;
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

} by {
    let { live: n, capacity: c } = unfold(st);
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
    have region->start == s by auto;
    have region->start + index + 1 <= e by {
        rewrite(region->start == s);
        assumption();
    }
    have 0 <= region->start + index by {
        rewrite(region->start == s);
        apply(int32_less_equal_transitive(0, s, s + index)) using {
            0 <= s;
            s <= s + index;
        }
    }
    have region->arena->capacity == c by {
        simp();
    }
    have region->start + index < region->arena->capacity by auto;
    have separate(memory(*region), memory(region->arena->data[s..e])) by auto;
    mark w;
    execute();
    transport(
        old(region->arena) == old(region->arena),
        region->arena == old(region->arena)
    ) using {
        at(w, separate(memory(*region), memory(region->arena->data[s..e])));
        s <= s + index;
        s + index + 1 <= e;
    }
    let r = fold(arena_region(region), { start: s, end: e });
    transport(old(region->arena->data) == old(region->arena->data),
        region->arena->data == old(region->arena->data)) using { }
    transport(old(region->arena->occupied) == old(region->arena->occupied),
        region->arena->occupied == old(region->arena->occupied)) using { }
    transport(old(region->arena->capacity) == old(region->arena->capacity),
        region->arena->capacity == old(region->arena->capacity)) using { }
    have separate(memory(region->arena->occupied[0..region->arena->capacity]), memory(region->arena->data[0..region->arena->capacity])) by {
        rewrite(region->arena->data == old(region->arena->data));
        rewrite(region->arena->occupied == old(region->arena->occupied));
        rewrite(region->arena->capacity == old(region->arena->capacity));
        assumption();
    }
    have separate(memory(*region->arena), memory(region->arena->data[0..region->arena->capacity])) by {
        rewrite(region->arena->data == old(region->arena->data));
        rewrite(region->arena->capacity == old(region->arena->capacity));
        rewrite(region->arena == old(region->arena));
        assumption();
    }
    have separate(memory(*region->arena), memory(region->arena->occupied[0..region->arena->capacity])) by {
        rewrite(region->arena->occupied == old(region->arena->occupied));
        rewrite(region->arena->capacity == old(region->arena->capacity));
        rewrite(region->arena == old(region->arena));
        assumption();
    }
    let st = fold(arena_state(region->arena), { live: n, capacity: c });
    simp();
}

```

```expect
pass
```
