# Reject missing contract at consuming close

The proof explicitly spends its owned member but the contract promises to
return it. Restoring the counter invariant does not restore the spent member.

```c filename=negative_consumption.c
struct counter { unsigned int value; };
unsigned int contribute_early(struct counter *p) {
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
    requires count(remaining(p)) > 1;
} by {
    with(control(p)) {
        have count(remaining(p)) - 1 >= 1 by {
            close() using {
                count(remaining(p)) > 1;
                count(remaining(p)) <= 3;
            };
        }
        have to_integer(p->value + 1u32) == 3 - to_integer(count(remaining(p)) - 1);
        have count(remaining(p)) - 1 <= 3 by {
            close() using { count(remaining(p)) > 1; count(remaining(p)) <= 3; };
        }
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
