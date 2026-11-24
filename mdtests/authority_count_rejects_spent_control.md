# Retired authority cannot create a new member

Consuming an empty authority preserves its proven zero count. That observation
does not restore authority or permit another membership change.

```c filename=spent_count.c
struct object { int32 refs; };
int32 spent_count() {
    struct object* obj = malloc(sizeof(struct object));
    if (obj == 0) { return -1; }
    obj->refs = 0;
    free(obj);
    return 0;
}
```

```click
authorized resource reference(obj: struct object*) {}

resource control(obj: struct object*) {
    owns obj->refs;
    owns authority(reference(obj));
    fact obj->refs == count(reference(obj));
}

verifying "spent_count.c";

int32 spent_count() {
    ensures result == -1 or result == 0;
} by {
    step();
    step();
    branch { true => { step(); close(); } false => {} }
    step();
    fold(authority(reference(obj)));
    fold(control(obj));
    unfold(control(obj));
    unfold(authority(reference(obj)));
    have count(reference(obj)) == 0 by close();
    fold(reference(obj));
}
```

```expect
fail: Requires owns authority(reference(p))
```
