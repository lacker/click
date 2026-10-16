# Archived object model rejects a bounded C pointer-field write

Priority: P2.

Soundness: not soundness. Recovery rejects a valid bounded write accepted by
its upstream baseline. This reproduction establishes a compatibility failure,
not a false acceptance. The repair must preserve object-domain rejection rules.

## Reproduction

At recovery checkpoint `c81242fbc`, save the following two files and run
`click verify original.click`. The complete proof rejects at
`arena_write.contract` tactic 12, reporting `pointer arithmetic left the
pointed-to object` for `arena->data + (region->start + index)`.
Upstream baseline `64f0f0d46` verifies the same complete proof with
`import click::machine_integer;` prepended for its modular standard library.
The baseline helper is linked from the identical Rust implementation at
`95fe8cbd1`. Both exit statuses were checked: recovery 1, baseline 0.

The C function and its contracts, resources and proof are extracted unchanged
from the original arena example. The trace establishes the slice ownership,
nonnegative index and sum, upper bound, and descriptor reads before rejection.
Opening `arena_initialized_storage` before execution exposes both allocation
holdings but still rejects at the same operation; hiding the allocation is not
a sufficient explanation. A simpler descriptor-and-slice control without the
full arena resources verifies on recovery. Do not infer a missing arithmetic
premise or a general inability to load C pointer fields from this failure.

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

```click filename=original.click
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
    ensures forall (k: int32) {
        0 <= k and k < region->arena->capacity implies
            region->arena->occupied[k] == old(region->arena->occupied[k])
    };
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
    mark w;
    execute();
    have forall (k: int32) {
        0 <= k and k < at(w, region->arena->capacity) implies
            at(w, region->arena->occupied[k]) == region->arena->occupied[k]
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < at(w, region->arena->capacity));
        simp();
    }
    let r = fold(arena_region(region), { start: s, end: e });
    let st = fold(arena_state(region->arena), { live: n, capacity: c });
    simp();
}

```

## Acceptance

- Verify this complete reproduction and the unchanged original arena write
  function; preserve its resource-held pointer and local descriptor alias.
- Preserve full pointer designation through the selected reads; do not turn
  numeric address equality, layout metadata, or allocation authority alone
  into arbitrary subobject or array-domain evidence.
- Retain scalar-subobject, wrong-object, one-past dereference and expired-object
  rejection controls, and protect selected lookup with deterministic scaling.
- Check fresh, expanded, rewritten and retained proofs. Rerun the normal
  example audit after the original project is restored; do not claim that the
  selected free proof alone restores arena.


## Recovery after the C input-read producer repair

Recovery `48a09a658` retains the exact full-pointer read at symbolic C input
without requiring native object enrollment. Its 34 pointer-domain controls and
160 selected read/store/native controls pass. The unchanged C store in this
reproduction now executes. Explicit descriptor-read and separation transport
gets both final resource folds through; the unchanged-occupancy postcondition
remains open. The original example's proof has not been replaced with an
incomplete isolated experiment.

A staged quantified occupancy transport also exposed speculative equality
instantiation costing more than the simple work allowance. Recovery
`85584a62c` restricts equality candidates to matching bound occurrences while
preserving intermediate order candidates; all 91 selected quantifier/transport
controls pass. The staged transport now reports a bounded missing-frame
refusal. Its reads agree in address and width, but the checked cell-history
walk does not yet justify the occupancy frame. Direct ownership of the
occupancy range verifies the reduced control; keeping the range inside the
child resource reproduces the refusal. Baseline `64f0f0d46` verifies the
complete staged reduction, including the child resource.

The full recovery audit remains last measured at 51/52. These candidate repairs
do not establish original-arena, retained-session or shared-model completion.


The next checked reduction locates the stopped history edge at the input cache
of `region->start`, recorded as a store rather than an observation. Naming
complete-object fields with the existing input producer and preserving exact
full-pointer observation bytes gets quantified occupancy transport through.
A guard rewrite using the established capacity equality closes the last goal.
Return-fold certification then rejects an unjustified path fact; the same
complete staged proof passes baseline `64f0f0d46`. This is the current blocker,
not a completed arena proof. Recovery's focused observation and native-control
selections pass (170 and 213 tests respectively).
