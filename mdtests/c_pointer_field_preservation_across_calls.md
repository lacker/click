# Complete pointer values survive unchanged C fields across modular calls

```c filename=preserve.c
struct box { int32 len; int32* data; };
void advance(struct box* owner) { owner->data[0] = 7; owner->len = 1; }
void renew(struct box* owner) { owner->len = 0; }
void caller(struct box* owner) { renew(owner); advance(owner); }
```

```click
resource storage(owner: struct box*) {
    owns owner->len;
    owns owner->data;
    owns owner->data[0..1];
    fact separate(memory(*owner), memory(owner->data[0..1]));
}
resource allocated(owner: struct box*) {
    owns owner->len;
    owns owner->data;
    owns owner->data[0..1];
    fact separate(memory(*owner), memory(owner->data[0..1]));
    owns allocation(owner->data, 4);
}
verifying "preserve.c";
void advance(struct box* owner) {
    owns storage(owner);
    ensures owner->data == old(owner->data);
} by {
    unfold(storage(owner));
    execute();
    have owner->data == old(owner->data) by simp;
    fold(storage(owner));
    assumption();
    assumption();
}
void renew(struct box* owner) {
    consumes allocated(owner);
    produces allocated(owner);
} by {
    unfold(allocated(owner));
    execute();
    fold(allocated(owner));
    assumption();
}
void caller(struct box* owner) {
    owns allocated(owner);
} by {
    step();
    unfold(allocated(owner));
    fold(storage(owner));
    execute();
    unfold(storage(owner));
    fold(allocated(owner));
    assumption();
}
```

```expect
pass
```
