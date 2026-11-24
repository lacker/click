# Iterated ownership: released cells feed an external claim

`recycle` holds two claimed cells `a` and `b` beside an empty window over the
gap between them. It clears both occupancy flags, gives both elements back to
the iterated clause, refolds the window at `a` with an empty owned prefix
`data[a..a]`, and hands it to the external `claim_run`. The call's transfer
includes that field-dependent empty range, which writes nothing, and the
occupancy map, which the window's `separate` fact keeps apart from the data
cells; the call checks the stored flags' facts against the transferred data
ranges through that separation. It isolates the call boundary of reusing
freed cells for a larger run, without a claim loop or a free-run proof, and
catches a call transition that
cannot use the separation fact or mishandles the empty write.

The proof shows that the indices differ before the second store. It uses
that separation to preserve the first zero flag before returning either
cell to the iterated clause.

```c filename=iterated_ownership_released_cells_feed_an_external_claim.c
extern void claim_run(int32* data, int32* occupied, int32 capacity, int32 start, int32 end);

void recycle(int32* data, int32* occupied, int32 capacity, int32 a, int32 b) {
    occupied[b] = 0;
    occupied[a] = 0;
    claim_run(data, occupied, capacity, a, b + 1);
}
```

```click
import click::separation;
resource arena_cells(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
}

resource arena_window(data: int32*, occupied: int32*, capacity: int32, start: int32, end: int32) {
    field next: int32;
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
    owns data[start..next];
    fact 0 <= start;
    fact start <= next;
    fact next <= end;
    fact end <= capacity;
    fact separate(memory(occupied[0..capacity]), memory(data[0..capacity]));
}

resource region(data: int32*, start: int32, end: int32) {
    owns data[start..end];
}

verifying "iterated_ownership_released_cells_feed_an_external_claim.c";

extern void claim_run(int32* data, int32* occupied, int32 capacity, int32 start, int32 end) {
    consumes w: arena_window(data, occupied, capacity, start, end);
    requires w.next == start;
    produces arena_cells(data, occupied, capacity);
    produces region(data, start, end);
}

void recycle(int32* data, int32* occupied, int32 capacity, int32 a, int32 b) {
    consumes gap: arena_window(data, occupied, capacity, a + 1, b);
    consumes region(data, a, a + 1);
    consumes region(data, b, b + 1);
    requires to_integer(gap.next) == to_integer(a + 1);
    requires 0 <= a;
    requires defined(a + 1);
    requires to_integer(a + 1) < to_integer(b);
    requires b < capacity;
    produces arena_cells(data, occupied, capacity);
    produces region(data, a, b + 1);
} by {
    unfold(gap);
    unfold(region(data, a, a + 1));
    unfold(region(data, b, b + 1));
    step();
    have occupied[b] == 0 by { close(); }
    have to_integer(a + 1) == to_integer(a) + 1 by {
        apply(click::integer::int32_add_to_integer(a, 1));
    }
    have a != b by {
        close() using { to_integer(a + 1) < to_integer(b); to_integer(a + 1) == to_integer(a) + 1; };
    }
    apply(separation::separate_elements(occupied, a, b));
    step();
    have separate(statement(1).footprint, memory(occupied[b])) by {
        normalize() using { separate(memory(occupied[a]), memory(occupied[b])); };
    }
    have occupied[b] == at(statement(1).entry, occupied[b]) by {
        preserve(memory(occupied[b]), statement(1));
    }
    have occupied[b] == 0 by {
        rewrite(occupied[b], at(statement(1).entry, occupied[b]));
        close();
    }
    have occupied[a] == 0 by { close(); }
    fold(arena_window(data, occupied, capacity, a + 1, b)[b]);
    fold(arena_window(data, occupied, capacity, a + 1, b)[a]);
    let w = fold(arena_window(data, occupied, capacity, a, b + 1), { next: a });
    have separate(memory(data[a..b + 1]), memory(occupied[0..capacity])) by close();
    step(claim_run, { w: w });
}
```

```expect
pass
```
