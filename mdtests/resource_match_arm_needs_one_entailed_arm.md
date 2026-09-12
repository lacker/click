# Excluding one constructor of three selects no arm

Arm selection is entailment, not search. `model != Slot::Empty` leaves both
`Slot::Reserved` and `Slot::Filled` possible, so no arm is selected, the
instance stays folded, and `requires node->value >= 0` is refused exactly as
it was before any arm could be selected at all.

There is no implicit proof by cases: the two surviving arms do not own the
same cells, and Click does not split the contract to find out which one the
caller meant. The diagnostic names the instance that stayed folded and the
field whose arm no requirement decides.

```c filename=threelower.c
struct cell { int32 value; };
int32 read_cell(struct cell *node) { return node->value; }
```

```click
verifying "threelower.c";

spec enum Slot { Empty, Reserved, Filled(int32) }

resource cell(p: struct cell*) {
    field model: Slot;
    match model {
        Slot::Empty => { fact p == 0; },
        Slot::Reserved => { fact p != 0; },
        Slot::Filled(value) => { owns p->value; fact p->value == value; },
    }
}

int32 read_cell(struct cell* node) {
    owns c: cell(node);
    requires c.model != Slot::Empty;
    requires node->value >= 0;
    ensures result >= 0;
} by {
    match c.model {
        Slot::Empty => { contradiction(c.model == Slot::Empty); },
        Slot::Reserved => { contradiction(c.model == Slot::Empty); },
        Slot::Filled(value) => {
            unfold(c);
            execute();
            let c = fold(cell(node), { model: Slot::Filled(value) });
            simp();
        },
    }
}
```

```expect
fail: `cell(node)` stays folded: no requirement of this contract selects one arm of its `model` field
```
