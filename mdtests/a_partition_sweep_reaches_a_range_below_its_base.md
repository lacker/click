# the partition sweep reaches a range that starts below its base

Two owners of one element is the partition violation the whole resource model
rests on: two owned ranges of one valid composition are pairwise separate, so a
write through one is framed away from a read through the other.

The gate over one block is a linear sweep whenever every owned range there has
constant endpoints at one base: sort by start, and compare each range against
the running range of greatest end, which is the only earlier range it can meet.
That is sound on the order the sweep assumes, and the sort key was the `u32`
bit pattern. `p[-1..1]` therefore sorted past every range there is, so its only
comparand was whichever range happened to sit at the top of the block — and
with one decoy in between, that is not `p[0..2]`, the range it shares element
`p[0]` with. The incremental route beside it probes the `concrete_memory`
key's immediate predecessor and successor and missed the same pair.

So `below_the_owner` owned `p[0]` twice, and:

    int32 write_then_read(int32* a, int32* b, int32 s, int32 e, int32 i) {
        int32 t;
        a[0] = 1;
        b[i] = 2;            //  b == a and i == 0: the same cell
        t = a[0];
        return t;
    }

verified `ensures result == 1` at `a == b == p`, `i == 0`, where it returns 2.
`write_then_read`'s own proof is right about its own precondition — it owns
`a[0..2]` and `b[s..e]` separately, so it may frame the store to `b[i]` away
from `a[0]`. The false step is the caller being allowed to instantiate that
precondition at `a == b`.

Both routes now sort and compare the signed numbers the endpoints are, and the
running maximum end is signed too, so a range whose end is below the base is
not taken as the furthest one. `beside_the_owner` is the positive next door:
the same three ranges where the one below the base really is disjoint, at
`p[-3..-1]`, still compose and still prove `result == 1` — which is true there,
because `b[-2]` is not `a[0]`.

```c filename=a_partition_sweep_reaches_a_range_below_its_base.c
int32 write_then_read(int32* a, int32* b, int32 s, int32 e, int32 i) {
    int32 t;
    a[0] = 1;
    b[i] = 2;
    t = a[0];
    return t;
}

int32 beside_the_owner(int32* p) {
    int32 ignored;
    int32 r;
    ignored = lend_below(p, -3, -1);
    r = write_then_read(p, p, -3, -1, -2);
    return r;
}

int32 below_the_owner(int32* p) {
    int32 ignored;
    int32 r;
    ignored = lend_below(p, -1, 1);
    r = write_then_read(p, p, -1, 1, 0);
    return r;
}
```

```click
import click::separation;
verifying "a_partition_sweep_reaches_a_range_below_its_base.c";

extern int32 lend_below(int32* r, int32 s, int32 e) {
    produces r[s..e];
}

int32 write_then_read(int32* a, int32* b, int32 s, int32 e, int32 i) {
    requires s <= i;
    requires i < e;
    owns a[0..2];
    owns a[5..6];
    consumes b[s..e];
    ensures result == 1;
} by {
    step();
    step();
    have a[0] == 1 by { close(); }
    have s <= e by { close() using { s <= i; i < e; }; }
    have separate(memory(a[0..2]), memory(b[s..e]));
    have contains(memory(a[0..2]), memory(a[0])) by { normalize(); }
    have i <= 2147483646 by { close() using { i < e; }; }
    have defined(i + 1) by { close() using { i <= 2147483646; }; }
    have i <= ((i + 1) as int32) by { close() using { i <= 2147483646; }; }
    have ((i + 1) as int32) <= e by { close() using { i < e; }; }
    have contains(memory(b[s..e]), memory(b[i..i+1])) by {
        apply(separation::contains_subrange(b, s, e, i, i+1));
    }
    have separate(memory(a[0]), memory(b[i..i+1])) by {
        apply(separation::separate_restrict(memory(a[0..2]), memory(b[s..e]), memory(a[0]), memory(b[i..i+1])));
    }
    have contains(memory(b[i..i+1]), memory(b[i])) by { normalize(); }
    have contains(memory(a[0]), memory(a[0])) by { normalize(); }
    have separate(memory(a[0]), memory(b[i])) by {
        apply(separation::separate_restrict(memory(a[0]), memory(b[i..i+1]), memory(a[0]), memory(b[i])));
    }
    mark before;
    step();
    have separate(statement(2).footprint, memory(a[0])) by {
        close();
    }
    have a[0] == at(before, a[0]) by {
        preserve(memory(a[0]), statement(2));
    }
    have a[0] == 1 by { normalize() using { a[0] == at(before, a[0]); at(before, a[0]) == 1; }; }
    step(); step();
}

int32 beside_the_owner(int32* p) {
    owns p[0..2];
    owns p[5..6];
    ensures result == 1;
}

int32 below_the_owner(int32* p) {
    owns p[0..2];
    owns p[5..6];
    ensures result == 1;
}
```

```expect
fail: overlapping owned memory resource facts `owns p[0..2]` and `owns p[-1..1]`
```
