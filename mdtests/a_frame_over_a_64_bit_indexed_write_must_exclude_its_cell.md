# A frame over a 64-bit indexed write must exclude its cell

A function stores `v` at a 64-bit index into a region whose length is a
64-bit member of an embedded struct. The frame clause omits `k != i`, so it
claims the written element is unchanged as well, which is false when `v`
differs from the old value. The transport must be refused; this catches a
64-bit quantified frame or a wide-range membership check that lets the
written cell through.

```c filename=a_frame_over_a_64_bit_indexed_write_must_exclude_its_cell.c
struct E { unsigned long n; };
struct S { struct E e; };
void set_at(int *p, const struct S *s, unsigned long i, int v) { p[i] = v; }
```

```click
verifying "a_frame_over_a_64_bit_indexed_write_must_exclude_its_cell.c";
void set_at(int32* p, const struct S* s, uint64 i, int32 v) {
    views s->e.n;
    owns p[0..s->e.n];
    requires i < s->e.n;
    ensures forall (k: uint64) { k < s->e.n implies p[k] == old(p[k]) };
} by {
    have 0u64 <= i by { close(); }
    have contains(memory(p[0u64..s->e.n]), memory(p[i])) by {
        apply(click::separation::contains_element(p, 0u64, s->e.n, i));
    }
    have contains(memory(s->e.n), memory(s->e.n)) by {
        apply(click::separation::contains_refl(memory(s->e.n)));
    }
    have separate(memory(p[i]), memory(s->e.n)) by {
        apply(click::separation::separate_restrict(memory(p[0u64..s->e.n]), memory(s->e.n), memory(p[i]), memory(s->e.n)));
    }
    step_until(function.exit);
    transport(
        forall (k: uint64) { k < s->e.n implies old(p[k]) == old(p[k]) },
        forall (k: uint64) { k < s->e.n implies p[k] == old(p[k]) }
    );
}
```

```expect
fail: found no frame evidence
```
