# Authority over an unauthorized family is refused

Population accounting covers only families declared `authorized resource`.
`reference` is an ordinary resource here, so `authority(reference(obj))`
names nothing and the declaration is refused.

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
resource reference(obj: struct object*) {}

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
    step();
    have count(reference(obj)) == 0 by close();
}
```

```expect
fail: `authority` names `reference`, which is not an authorized family
```
