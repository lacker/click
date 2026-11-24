# A nested call cannot hide a second consumption at return

The first contribution and the nested helper each spend one member. Although
the control is restored, the contract promises to consume only one and return
the other; that return fails after the second spend.

```c filename=overconsume.c
struct counter { unsigned int value; };
unsigned int contribute_early(struct counter *p) {
    p->value = p->value + 1u;
    return p->value;
}
unsigned int overconsume(struct counter *p) {
    p->value = p->value + 1u;
    return contribute_early(p);
}
```

```click
verifying "overconsume.c";
authorized resource remaining(p: struct counter*) {}
resource control(p: struct counter*) {
    owns authority(remaining(p));
    owns p->value;
    fact count(remaining(p)) <= 3;
    fact p->value == 3 - count(remaining(p));
}
uint32 contribute_early(struct counter* p) {
    owns control(p);
    consumes remaining(p);
    requires count(remaining(p)) > 1;
} by {
    with(control(p)) { have count(remaining(p)) <= 3; }
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
uint32 overconsume(struct counter* p) {
    owns control(p);
    owns remaining(p);
    consumes remaining(p);
    requires count(remaining(p)) > 2;
} by {
    have count(remaining(p)) > 1 by { close() using { count(remaining(p)) > 2; }; }
    with(control(p)) { have count(remaining(p)) <= 3; }
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
        have count(remaining(p)) - 1 > 1 by { close() using { count(remaining(p)) > 2; count(remaining(p)) <= 3; }; }
        unfold(remaining(p));
        step();
    }
    step();
    step();
    close();
}
```

```expect
fail: missing resource fact `owns remaining(p)`
```
