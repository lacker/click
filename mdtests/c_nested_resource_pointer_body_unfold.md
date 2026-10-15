# A nested C resource can expose and restore a pointer-backed body

The resources retain the original ring-buffer nesting. Opening the outer
head and then the inner head must preserve memory while exposing their bodies.
The wrapper performs no C memory operation.

```c filename=probe.c
struct ring_buffer { int32 head; int32 tail; int32* data; };
int32 probe(struct ring_buffer* owner) { return 0; }
```

```click
resource ring_frame(owner: struct ring_buffer*) {
    owns owner->head;
    owns owner->data;
    owns owner->data[0..4];
    fact 2 <= owner->head;
    fact owner->head < 4;
    fact separate(memory(*owner), memory(owner->data[0..4]));
}

resource linear_ring(owner: struct ring_buffer*) {
    owns owner->tail;
    owns ring_frame(owner);
    fact owner->tail == 4;
}

verifying "probe.c";
int32 probe(struct ring_buffer* owner) {
    owns linear_ring(owner);
    ensures result == 0;
} by {
    unfold(linear_ring(owner));
    unfold(ring_frame(owner));
    execute();
    fold(ring_frame(owner));
    fold(linear_ring(owner));
    simp();
}
```

```expect
pass
```
