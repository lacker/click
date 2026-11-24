# Reject repeated at consuming close

Both unchanged C increments can be matched by explicit member consumptions
while the control is open. The contract permits one consumption and promises
to return the other member, so restoring the counter invariant cannot close
the proof after both members have been spent.

```c filename=negative_consumption.c
struct counter { unsigned int value; };
unsigned int contribute_early(struct counter *p) {
    p->value = p->value + 1u;
    p->value = p->value + 1u;
    return p->value;
}
```

```click
verifying "negative_consumption.c";
authorized resource remaining(p: struct counter*) {}
resource control(p: struct counter*) {
    owns authority(remaining(p));
    owns p->value;
    fact count(remaining(p)) <= 3;
    fact p->value == 3 - count(remaining(p));
}
uint32 contribute_early(struct counter* p) {
    owns control(p);
    owns remaining(p);
    consumes remaining(p);
    requires count(remaining(p)) > 1;
} by {
    with(control(p)) {
        have to_integer((p->value + 1u32) + 1u32) == 3 - to_integer(count(remaining(p)) - 2);
        have count(remaining(p)) - 2 <= 3 by {
            close() using { count(remaining(p)) > 1; count(remaining(p)) <= 3; };
        }
        unfold(remaining(p));
        step();
        unfold(remaining(p));
        step();
    }
    with(control(p)) { step(); }
    close();
}

```

```expect
fail: missing resource fact `owns remaining(p)`
```
