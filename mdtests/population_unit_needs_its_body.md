# A population unit is produced only with its body

A counted population's body is population-wide, and a unit of it exists
only once that body has been folded into the family. A verified producer
that owns nothing of the body cannot mint a unit: the fold demands the
body's memory. This is what lets a produced unit skip the produced-body
overlap check, since the bytes it packages left the producer's context.

```click
resource ref(o: struct s*) {
    owns o->x;
}

predicate live(o: struct s*) {
    1 <= count(ref(o))
}

verifying "mint.c";

int32 mint(struct s* o) {
    requires o != 0;
    requires count(ref(o)) == 0;
    produces 1 of ref(o);
} by {
    execute();
    fold(1 of ref(o));
    simp();
}
```

```c filename=mint.c
struct s { int32 x; };
int32 mint(struct s* o) { return 0; }
```

```expect
fail: missing resource fact `owns o[0..1]`
```
