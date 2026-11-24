# A correctly typed model pointer grants no view authority

Recovering the declared byte element type permits theorem argument capture,
while its viewability prerequisite still requires a checked memory view.

```c filename=simple.c
void keep(const uint8* p, int32 i) {}
```

```click
verifying "simple.c";
spec enum Link { Node(const uint8*) }
resource Cell(p: const uint8*, i: int32) {
 field model: Link;
 match model { Link::Node(q) => { fact q == p; }, }
}
theorem bounded_pointer_association(base: const uint8*, index: int32) {
 requires 0 <= index;
 requires index <= 22200;
 ensures (base + index) + 4 == base + (index + 4) by {
  have defined(index + 4) by { close() using { 0 <= index; index <= 22200; }; }
  normalize() using { defined(index + 4); };
 }
}
theorem readable_byte_pointer(base: const uint8*) {
 requires viewable(base[0..4]);
 ensures viewable(base[0..4]) by close();
}
void keep(const uint8* p, int32 i) {
 requires 0 <= i;
 requires i <= 22200;
 owns h: Cell(p, i);
} by {
 match h.model {
  Link::Node(q) => {
   unfold(h);
   have viewable(q[0..4]) by { apply(readable_byte_pointer(q)); }
   let h = fold(Cell(p, i), { model: Link::Node(q) });
  },
 }
}

```

```expect
fail: viewable
```
