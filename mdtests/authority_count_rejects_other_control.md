# A control authorizes only its own population count

The authority contained in `control(first)` does not justify an observation
of `reference(second)`. The two parameters may denote distinct populations.

```c filename=wrong_count.c
struct object { int32 refs; };
void wrong_count(struct object* first, struct object* second) {}
```

```click
authorized resource reference(obj: struct object*) {}

resource control(obj: struct object*) {
    owns obj->refs;
    owns authority(reference(obj));
    fact obj->refs == count(reference(obj));
}

verifying "wrong_count.c";

void wrong_count(struct object* first, struct object* second) {
    owns control(first);
} by {
    have count(reference(second)) == 0 by close();
}
```

```expect
fail: count(...) requires owning authority for that population
```
