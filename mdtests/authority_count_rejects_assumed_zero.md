# A folded control does not imply an empty population

An external control authenticates an arbitrary entry count. Owning that control
permits an observation; it does not establish that the count is zero.

```c filename=assumed_zero.c
struct object { int32 refs; };
void assumed_zero(struct object* obj) {}
```

```click
authorized resource reference(obj: struct object*) {}

resource control(obj: struct object*) {
    owns obj->refs;
    owns authority(reference(obj));
    fact obj->refs == count(reference(obj));
}

verifying "assumed_zero.c";

void assumed_zero(struct object* obj) {
    owns control(obj);
} by {
    have count(reference(obj)) == 0 by close();
}
```

```expect
fail: could not establish `to_integer(count(reference(obj))) == 0`
```
