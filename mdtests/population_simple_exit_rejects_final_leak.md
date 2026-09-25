# A simple closer cannot discard the final population allocation

The final release restores the logical count but omits `free`. Completing
its pure postcondition with a simple tactic must still check the allocation
obligation when applying the return-resource exchange.

```c filename=leak.c
struct object { int32 refs; };
void release(struct object* obj) { obj->refs = 0; }
```

```click
resource reference(obj: struct object*) {
    contains allocation(obj, sizeof(struct object));
    owns object(obj);
    fact obj->refs == count(reference(obj));
}
verifying "leak.c";
void release(struct object* obj) {
    requires count(reference(obj)) == 1;
    consumes reference(obj);
    ensures 0 == 0;
} by {
    unfold(reference(obj));
    execute();
    normalize();
}
```

```expect
fail: live allocation obligation
```
