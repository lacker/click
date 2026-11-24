# A loop frame keeps a two-hop map beside a written array

`clear_data` reaches the arena through its region descriptor, copies the
pointer into a local, and clears `arena->data` in a loop that owns only that
array. The loop invariant frames the occupancy map through both hops of the
descriptor, `region->arena->occupied[k] == old(region->arena->occupied[k])`,
and the preservation proof uses explicit separation and preservation of the
pointer fields and selected map cell. The data pointer's loop-entry identity
keeps its original array bounds available to the C store. Separation invariants
retain the frame evidence while the descriptor owners are borrowed as views.
The proof names each unchanged pointer before using it to compare the map
read with its value at the start of the iteration.

```c filename=loop_frame_keeps_a_two_hop_map_beside_a_written_array.c
struct arena {
    int32* data;
    int32* occupied;
    int32 capacity;
};

struct region {
    struct arena* arena;
};

void clear_data(struct region* region) {
    struct arena* arena;
    int32 i;
    arena = region->arena;
    i = 0;
    while (i < arena->capacity) {
        arena->data[i] = 0;
        i = i + 1;
    }
}
```

```click
verifying "loop_frame_keeps_a_two_hop_map_beside_a_written_array.c";

void clear_data(struct region* region) {
    owns *region;
    owns *region->arena;
    owns region->arena->data[0..region->arena->capacity];
    owns region->arena->occupied[0..region->arena->capacity];
    requires 0 <= region->arena->capacity;
} by {
    step();
    step();
    step();
    step();
    have separate(memory(arena->data[0..arena->capacity]), memory(*arena)) by { close(); }
    have contains(memory(arena->data[0..arena->capacity]), memory(arena->data[0..arena->capacity])) by { apply(click::separation::contains_refl(memory(arena->data[0..arena->capacity]))); }
    have contains(memory(*arena), memory(arena->data)) by {
        apply(click::separation::contains_subrange(arena as (int32*), 0, 6, 0, 2));
    }
    have separate(memory(arena->data[0..arena->capacity]), memory(arena->data)) by {
        apply(click::separation::separate_restrict(memory(arena->data[0..arena->capacity]), memory(*arena), memory(arena->data[0..arena->capacity]), memory(arena->data)));
    }
    have contains(memory(*arena), memory(region->arena->occupied)) by {
        apply(click::separation::contains_subrange(arena as (int32*), 0, 6, 2, 4));
    }
    have separate(memory(arena->data[0..arena->capacity]), memory(region->arena->occupied)) by {
        apply(click::separation::separate_restrict(memory(arena->data[0..arena->capacity]), memory(*arena), memory(arena->data[0..arena->capacity]), memory(region->arena->occupied)));
    }
    have contains(memory(*arena), memory((arena as (int32*))[4..5])) by {
        apply(click::separation::contains_subrange(arena as (int32*), 0, 6, 4, 5));
    }
    have contains(memory((arena as (int32*))[4..5]), memory((&arena->capacity)[0..1])) by {
        apply(click::separation::contains_rebase(arena as (int32*), 4, 5));
    }
    have contains(memory(*arena), memory((&arena->capacity)[0..1])) by {
        apply(click::separation::contains_trans(memory(*arena), memory((arena as (int32*))[4..5]), memory((&arena->capacity)[0..1])));
    }
    have separate(memory(arena->data[0..arena->capacity]), memory((&arena->capacity)[0..1])) by {
        apply(click::separation::separate_restrict(memory(arena->data[0..arena->capacity]), memory(*arena), memory(arena->data[0..arena->capacity]), memory((&arena->capacity)[0..1])));
    }
    have separate(memory(arena->data[0..arena->capacity]), memory(region->arena)) by { close(); }
    have separate(memory(arena->data[0..arena->capacity]), memory(region->arena->occupied[0..arena->capacity])) by { close(); }
    loop {
        decreases (arena->capacity - i);
        owns arena->data[0..arena->capacity];
        // Retain frame evidence while the descriptor owners are borrowed as views.
        invariant separate(memory(arena->data[0..arena->capacity]), memory(arena->data));
        invariant separate(memory(arena->data[0..arena->capacity]), memory(region->arena));
        invariant separate(memory(arena->data[0..arena->capacity]), memory(region->arena->occupied));
        invariant separate(memory(arena->data[0..arena->capacity]), memory(region->arena->occupied[0..arena->capacity]));
        invariant separate(memory(arena->data[0..arena->capacity]), memory((&arena->capacity)[0..1]));
        invariant arena->data == at(loop(0).entry, arena->data);
        invariant 0 <= i and i <= arena->capacity;
        invariant forall (k: int32) { 0 <= k and k < arena->capacity implies region->arena->occupied[k] == old(region->arena->occupied[k]) };
        initialize by close();
        maintain by {
            mark opened;
            have contains(memory(arena->data[0..arena->capacity]), memory(arena->data[i])) by {
                apply(click::separation::contains_element(arena->data, 0, arena->capacity, i));
            }
            have separate(memory(arena->data[0..arena->capacity]), memory(arena->data)) by { close(); }
            have separate(memory(arena->data[0..arena->capacity]), memory(region->arena)) by { close(); }
            have separate(memory(arena->data[0..arena->capacity]), memory(region->arena->occupied)) by { close(); }
            have separate(memory(arena->data[0..arena->capacity]), memory(region->arena->occupied[0..arena->capacity])) by { close(); }
            have contains(memory(arena->data), memory(arena->data)) by { apply(click::separation::contains_refl(memory(arena->data))); }
            have separate(memory(arena->data[i]), memory(arena->data)) by {
                apply(click::separation::separate_restrict(memory(arena->data[0..arena->capacity]), memory(arena->data), memory(arena->data[i]), memory(arena->data)));
            }
            have contains(memory(region->arena), memory(region->arena)) by { apply(click::separation::contains_refl(memory(region->arena))); }
            have separate(memory(arena->data[i]), memory(region->arena)) by {
                apply(click::separation::separate_restrict(memory(arena->data[0..arena->capacity]), memory(region->arena), memory(arena->data[i]), memory(region->arena)));
            }
            have contains(memory(region->arena->occupied), memory(region->arena->occupied)) by { apply(click::separation::contains_refl(memory(region->arena->occupied))); }
            have separate(memory(arena->data[i]), memory(region->arena->occupied)) by {
                apply(click::separation::separate_restrict(memory(arena->data[0..arena->capacity]), memory(region->arena->occupied), memory(arena->data[i]), memory(region->arena->occupied)));
            }
            have separate(memory(arena->data[0..arena->capacity]), memory((&arena->capacity)[0..1])) by { close(); }
            have contains(memory((&arena->capacity)[0..1]), memory((&arena->capacity)[0..1])) by { apply(click::separation::contains_refl(memory((&arena->capacity)[0..1]))); }
            have separate(memory(arena->data[i]), memory((&arena->capacity)[0..1])) by {
                apply(click::separation::separate_restrict(memory(arena->data[0..arena->capacity]), memory((&arena->capacity)[0..1]), memory(arena->data[i]), memory((&arena->capacity)[0..1])));
            }
            step();
            have separate(loop(0).statement(0).footprint, at(opened, memory(arena->data))) by {
                close() using { at(opened, separate(memory(arena->data[i]), memory(arena->data))); };
            }
            have separate(loop(0).statement(0).footprint, at(opened, memory(region->arena))) by {
                close() using { at(opened, separate(memory(arena->data[i]), memory(region->arena))); };
            }
            have separate(loop(0).statement(0).footprint, at(opened, memory(region->arena->occupied))) by {
                close() using { at(opened, separate(memory(arena->data[i]), memory(region->arena->occupied))); };
            }
            have arena->data == at(opened, arena->data) by {
                preserve(at(opened, memory(arena->data)), loop(0).statement(0));
            }
            have region->arena == at(opened, region->arena) by {
                preserve(at(opened, memory(region->arena)), loop(0).statement(0));
            }
            // First preserve the pointer at a fixed address, then substitute the outer hop.
            have at(opened, region->arena)->occupied == at(opened, region->arena->occupied) by {
                preserve(at(opened, memory(region->arena->occupied)), loop(0).statement(0));
            }
            have region->arena->occupied == at(opened, region->arena->occupied) by {
                rewrite(region->arena, at(opened, region->arena));
                close();
            }
            // Select the complete int32 cell, excluding the struct's tail padding.
            have separate(loop(0).statement(0).footprint, at(opened, memory((&arena->capacity)[0..1]))) by {
                close() using { at(opened, separate(memory(arena->data[i]), memory((&arena->capacity)[0..1]))); };
            }
            have arena->capacity == at(opened, arena->capacity) by {
                preserve(at(opened, memory((&arena->capacity)[0..1])), loop(0).statement(0));
            }
            have forall (k: int32) { 0 <= k and k < arena->capacity implies region->arena->occupied[k] == old(region->arena->occupied[k]) } by {
                intro(); intro();
                have k < at(opened, arena->capacity) by { close(); }
                have contains(at(opened, memory(region->arena->occupied[0..arena->capacity])), at(opened, memory(region->arena->occupied[k]))) by {
                    apply(click::separation::contains_element(at(opened, region->arena->occupied), 0, at(opened, arena->capacity), k));
                }
                have separate(at(opened, memory(arena->data[i])), at(opened, memory(region->arena->occupied[k]))) by {
                    apply(click::separation::separate_restrict(at(opened, memory(arena->data[0..arena->capacity])), at(opened, memory(region->arena->occupied[0..arena->capacity])), at(opened, memory(arena->data[i])), at(opened, memory(region->arena->occupied[k]))));
                }
                // Select the preserved cell as one complete int32 observation.
                have contains(at(opened, memory(region->arena->occupied[k])), at(opened, memory((&region->arena->occupied[k])[0..1]))) by { normalize(); }
                have contains(at(opened, memory(arena->data[i])), at(opened, memory(arena->data[i]))) by { apply(click::separation::contains_refl(at(opened, memory(arena->data[i])))); }
                have separate(at(opened, memory(arena->data[i])), at(opened, memory((&region->arena->occupied[k])[0..1]))) by {
                    apply(click::separation::separate_restrict(at(opened, memory(arena->data[i])), at(opened, memory(region->arena->occupied[k])), at(opened, memory(arena->data[i])), at(opened, memory((&region->arena->occupied[k])[0..1]))));
                }
                have separate(loop(0).statement(0).footprint, at(opened, memory((&region->arena->occupied[k])[0..1]))) by {
                    close();
                }
                have at(loop(0).statement(0).exit, load<int32>(at(opened, &region->arena->occupied[k])))
                        == at(loop(0).statement(0).entry, load<int32>(at(opened, &region->arena->occupied[k]))) by {
                    preserve(at(opened, memory((&region->arena->occupied[k])[0..1])), loop(0).statement(0));
                }
                have region->arena->occupied[k] == at(opened, region->arena->occupied[k]) by {
                    rewrite(region->arena->occupied, at(opened, region->arena->occupied));
                    close();
                }
                instantiate(at(opened, forall (j: int32) { 0 <= j and j < arena->capacity implies region->arena->occupied[j] == old(region->arena->occupied[j]) }), k);
                close();
            }
            step();
            have arena->data == at(loop(0).entry, arena->data) by {
                rewrite(arena->data, at(opened, arena->data));
                close();
            }
            have separate(memory(arena->data[0..arena->capacity]), memory(arena->data)) by {
                rewrite(arena->data, at(opened, arena->data));
                rewrite(arena->capacity, at(opened, arena->capacity));
                close();
            }
            have separate(memory(arena->data[0..arena->capacity]), memory(region->arena)) by {
                rewrite(arena->data, at(opened, arena->data));
                rewrite(arena->capacity, at(opened, arena->capacity));
                close();
            }
            have separate(memory(arena->data[0..arena->capacity]), memory(region->arena->occupied)) by {
                rewrite(arena->data, at(opened, arena->data));
                rewrite(arena->capacity, at(opened, arena->capacity));
                rewrite(region->arena, at(opened, region->arena));
                close();
            }
            have separate(memory(arena->data[0..arena->capacity]), memory(region->arena->occupied[0..arena->capacity])) by {
                rewrite(arena->data, at(opened, arena->data));
                rewrite(arena->capacity, at(opened, arena->capacity));
                rewrite(region->arena->occupied, at(opened, region->arena->occupied));
                close();
            }
            have separate(memory(arena->data[0..arena->capacity]), memory((&arena->capacity)[0..1])) by {
                rewrite(arena->data, at(opened, arena->data));
                rewrite(arena->capacity, at(opened, arena->capacity));
                close();
            }
            have arena->capacity == at(opened, arena->capacity) by { close(); }
            have 0 <= at(opened, i) by { close(); }
            have at(opened, i) <= 2147483646 by {
                close() using { at(opened, i) < at(opened, arena->capacity); };
            }
            // Relate the machine increment to its exact Integer value.
            have -2147483648 <= to_integer(at(opened, i)) + 1 by {
                close() using { 0 <= at(opened, i); };
            }
            have to_integer(at(opened, i)) + 1 <= 2147483647 by {
                close() using { at(opened, i) <= 2147483646; };
            }
            have to_integer(i) == to_integer(at(opened, i)) + 1 by {
                close() using {
                    -2147483648 <= to_integer(at(opened, i)) + 1;
                    to_integer(at(opened, i)) + 1 <= 2147483647;
                };
            }
            have 0 <= i and i <= arena->capacity by {
                close() using {
                    0 <= at(opened, i);
                    at(opened, i) < at(opened, arena->capacity);
                    arena->capacity == at(opened, arena->capacity);
                    to_integer(i) == to_integer(at(opened, i)) + 1;
                };
            }
            close();
        }
    }
    step();
    close();
}
```

```expect
pass
```
