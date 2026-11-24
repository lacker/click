# A child path follows its exposed instance

A child path reads through the parent while it is folded and names the
exposed child when opened. The path and an explicit alias then agree. A
nested with closes the same child and parent without any output map.

```c filename=child_paths.c
void by_unfold(void) {}
void by_scope(void) {}
```

```click
verifying "child_paths.c";

resource leaf() { field tag: int32; }
resource inner() { owns item: leaf(); }
resource outer() { owns child: inner(); }

tactic keep_tag() {
    owns slot: leaf();
    ensures slot.tag == old(slot.tag);
} by { have slot.tag == old(slot.tag) by close(); }

void by_unfold() {
    owns r: outer();
    ensures r.child.item.tag == old(r.child.item.tag);
} by {
    let { child: c } = unfold(r);
    unfold(r.child);
    observe(r.child.item);
    keep_tag({ slot: r.child.item });
    have r.child.item.tag == old(r.child.item.tag) by close();
    unfold(r.child.item);
    have r.child.item.tag == old(r.child.item.tag) by close();
    fold(r.child.item);
    fold(c);
    fold(r);
}

void by_scope() {
    owns r: outer();
    ensures r.child.item.tag == old(r.child.item.tag);
} by {
    with(r) {
        with(r.child) {
            have r.child.item.tag == old(r.child.item.tag) by close();
            step_until(function.exit);
        }
    }
}
```

```expect
pass
```
