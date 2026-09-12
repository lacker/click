# An existential requirement selects a matched arm at contract lowering

`exists (v: int32) { c.model == Maybe::Some(v) }` names the arm without naming
its payload, and that is enough to select it. Both arms of this model own the
same cell, but a matched resource exposes nothing until one arm is selected,
so `requires node->value >= 0` is refused without the existential requirement
and accepted with it.

The proof still names the payload itself, through the constructor cases the
`match` tactic introduces.

```c filename=existslower.c
struct cell { int32 value; };
int32 read_cell(struct cell *node) { return node->value; }
```

```click
verifying "existslower.c";

spec enum Maybe { None, Some(int32) }

resource cell(p: struct cell*) {
    field model: Maybe;
    match model {
        Maybe::None => { owns p->value; fact p->value == 0; },
        Maybe::Some(value) => { owns p->value; fact p->value == value; },
    }
}

int32 read_cell(struct cell* node) {
    owns c: cell(node);
    requires exists (v: int32) { c.model == Maybe::Some(v) };
    requires node->value >= 0;
    ensures result >= 0;
} by {
    match c.model {
        Maybe::None => { unfold(c); execute(); fold(c); simp(); },
        Maybe::Some(value) => { unfold(c); execute(); fold(c); simp(); },
    }
}
```

```expect
pass
```
