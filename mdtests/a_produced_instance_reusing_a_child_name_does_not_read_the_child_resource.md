# A produced instance that reuses a child's name does not read the child's resource

`x` first names the `cellA` child an unfold takes from `root`. After the
fold returns it, `step(mk)` binds `x` again, to the `cellB` instance
`mk` produces. `cellB` declares `v` second, so `x.v` must read the second
field, which `mk` sets to 1.
The negative twin of
[`a_produced_instance_reusing_a_child_name_reads_its_own_fields.md`](a_produced_instance_reusing_a_child_name_reads_its_own_fields.md).
Before, `x.v` read `cellA`'s first field, `w` here, which `mk` sets to 42,
so this false claim verified.

```c filename=a_produced_instance_reusing_a_child_name_does_not_read_the_child_resource.c
void mk(int32* p);
void f(int32* q, int32* p2) { mk(p2); }
```

```click
verifying "a_produced_instance_reusing_a_child_name_does_not_read_the_child_resource.c";

resource cellA(p: int32*) {
    field v: int32;
    owns p[0..1];
    fact p[0] == v;
}

resource cellB(p: int32*) {
    field w: int32;
    field v: int32;
    owns p[0..1];
    fact p[0] == v;
}

resource root(q: int32*) {
    field u: int32;
    owns k: cellA(q);
    fact k.v == u;
}

extern void mk(int32* p) {
    consumes p[0..1];
    produces first: cellB(p);
    ensures first.v == 1;
    ensures first.w == 42;
}

void f(int32* q, int32* p2) {
    owns r: root(q);
    consumes p2[0..1];
} by {
    let { k: x, u: ru } = unfold(r);
    let r = fold(root(q), { u: ru, k: x });
    let { first: x } = step(mk);
    have x.v == 42 by { close(); }
    step();
    close();
}
```

```expect
fail: could not establish
```
