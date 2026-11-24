# a binder map on an inline helper with no contract is refused

A `static inline` helper with no Click contract runs its checked body at the
call site, on the caller's own resources. There is no contract boundary, so a
call step's binder map, `step(fill, { x: x })`, names a binder that does
not exist and is refused by name. With a contract, the same step selects the helper's binders
([`call_step_binder_map_selects_an_inline_helpers_contract.md`](call_step_binder_map_selects_an_inline_helpers_contract.md)).

```c filename=call_step_binder_map_on_an_uncontracted_inline_helper_rejected.c
struct cell { unsigned long word; };

static inline __attribute__((always_inline)) void fill(struct cell *p) {
    p->word = 1;
}

void caller(struct cell *p) {
    fill(p);
}
```

```click
verifying "call_step_binder_map_on_an_uncontracted_inline_helper_rejected.c";

resource filled(p: struct cell*) {
    field tag: int32;
    owns p->word;
}

void caller(struct cell* p) {
    consumes x: filled(p);
    produces y: filled(p);
} by {
    let { result: y } = step(fill, { x: x });
    close();
}
```

```expect
fail: `fill` declares no resource instance binder `x`
```
