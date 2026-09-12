# A loop binder under a fresh name is refused by name

D5's rule is that a loop binder reuses the enclosing binder's name: the loop
takes over that instance for the body and hands it back at the back edge. A
fresh name consumes the enclosing one for the rest of the function, so it names
nothing before the loop, and an invariant that reads it at loop entry has
nothing to read.

That used to surface as the bare `could not lower entry invariants: Paths`,
which names neither the loop, the binder, nor the rule. The refusal now names
the binder and says what to write instead.

```c filename=loop_binder_rejects_fresh_name_in_invariant.c
struct cell { int32 value; };

void bump_n(struct cell* p, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        p->value = p->value + 1;
        i = i + 1;
    }
}
```

```click
verifying "loop_binder_rejects_fresh_name_in_invariant.c";

resource counter(p: struct cell*) {
    field count: int32;
    owns p->value;
    fact p->value == count;
}

void bump_n(struct cell* p, int32 n) {
    requires n >= 0;
    requires n <= 1000;
    owns c: counter(p);
    requires c.count == 0;
    ensures c.count == old(c.count) + n;
} by {
    step();
    step();
    loop {
        owns d: counter(p);
        invariant i >= 0;
        invariant i <= n;
        invariant d.count == old(c.count) + i;

        initialize by simp;
        preserve by {
            unfold(d);
            step();
            step();
            let d = fold(counter(p), { count: old(c.count) + i });
            close_invariants();
        }
    }
    have i == n by simp;
    execute();
    simp();
}
```

```expect
fail: loop binder `d` is not an enclosing contract binder
```
