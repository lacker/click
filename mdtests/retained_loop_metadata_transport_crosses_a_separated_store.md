# Explicit field preservation after a store inside an ownership loop
```c filename=probe.c
struct arena { int32* data; int32* occupied; int32 capacity; };
struct region { struct arena* arena; int32 start; int32 end; };
void clear(struct region* region) {
    struct arena* arena = region->arena;
    int32 i = region->start;
    while (i < region->end) {
        arena->occupied[i] = 0;
        return;
    }
}
```
```click
resource arena_clear_window(
    data: int32*,
    occupied: int32*,
    capacity: int32,
    start: int32,
    end: int32
) {
    field next: int32;
    owns occupied[0..capacity];
    owns data[next..end];
    fact 0 <= start;
    fact start <= next;
    fact next <= end;
    fact end <= capacity;
    fact separate(memory(occupied[0..capacity]), memory(data[0..capacity]));
    fact forall (k: int32) {
        start <= k and k < next implies occupied[k] == 0
    };
}

verifying "probe.c";
void clear(struct region* region) {
    owns *region;
    owns *region->arena;
    consumes w: arena_clear_window(region->arena->data, region->arena->occupied,
        region->arena->capacity, region->start, region->end);
    requires w.next == region->start;
    requires separate(memory(*region), memory(region->arena->occupied[0..region->arena->capacity]));
} by {
    step(); step(); step(); step();
    loop scan {
        decreases to_integer(region->end) - to_integer(i);
        owns w: arena_clear_window(arena->data, arena->occupied, arena->capacity, region->start, region->end);
        invariant w.next == i;
        invariant separate(memory(*region), memory(arena->occupied[0..arena->capacity]));
        initialize by close();
        maintain by {
            let { next: m } = unfold(w);
            have m == i;
            have 0 <= i;
            have i < arena->capacity;
            have contains(memory(*region), memory(region->start)) by { normalize(); }
            have contains(memory(arena->occupied[0..arena->capacity]), memory(arena->occupied[i])) by {
                apply(click::separation::contains_element(arena->occupied, 0, arena->capacity, i));
            }
            have separate(memory(region->start), memory(arena->occupied[i])) by {
                apply(click::separation::separate_restrict(memory(*region), memory(arena->occupied[0..arena->capacity]), memory(region->start), memory(arena->occupied[i])));
            }
            mark opened;
            step();
            have separate(loop(0).statement(0).footprint, memory(region->start)) by {
                close() using { at(opened, separate(memory(region->start), memory(arena->occupied[i]))); };
            }
            have region->start == at(opened, region->start) by {
                preserve(memory(region->start), loop(0).statement(0));
            }
            step();
        }
    }
}
```
```expect
pass
```
