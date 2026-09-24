# A contract returns an instance whose argument a field-bearing sibling supplies

The return-side twin of
[`contract_owns_through_field_bearing_instance.md`](contract_owns_through_field_bearing_instance.md).
`probe` borrows `r: prefix_region(region)`, which carries a plain field and
owns the region descriptor, and `st: live_count(region->arena)`, whose argument
loads `region->arena` from a cell `r` owns. Both are returned when the body
finishes, still folded.

Returning a borrowed instance reads its clause again, so `region->arena` has to
be addressable at the return exactly as it was at entry. The folded `r`
publishes the cells its unconditional, unmatched body owns as read authority
for the other returned clauses, the same publication the entry section makes,
and the postcondition `st.live == old(st.live)` names the returned instance
through it. Nothing is unfolded, and clause order does not decide the
contract: `probe_reversed` states the two clauses the other way round.

```c filename=probe.c
struct arena {
    int32* data;
    int32 live_regions;
};

struct region {
    struct arena* arena;
    int32 start;
};

void probe(struct region* region) {
}

void probe_reversed(struct region* region) {
}
```

```click
resource live_count(arena: struct arena*) {
    field live: int32;
    owns arena->live_regions;
}

resource prefix_region(region: struct region*) {
    field start: int32;
    owns object(region);
}

verifying "probe.c";

void probe(struct region* region) {
    owns r: prefix_region(region);
    owns st: live_count(region->arena);

    ensures r.start == old(r.start);
    ensures st.live == old(st.live);
} by {
    execute();
    simp();
}

void probe_reversed(struct region* region) {
    owns st: live_count(region->arena);
    owns r: prefix_region(region);

    ensures r.start == old(r.start);
    ensures st.live == old(st.live);
} by {
    execute();
    simp();
}
```

```expect
pass
```
