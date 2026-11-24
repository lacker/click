# Reject wrong increment at consuming close

```c filename=negative_consumption.c
struct counter { unsigned int value; };
unsigned int contribute_early(struct counter *p) {
    p->value = p->value + 2u;
    
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
    consumes remaining(p);
    requires count(remaining(p)) > 1;
} by {
    with(control(p)) {
        have count(remaining(p)) - 1 >= 1 by {
            close() using {
                count(remaining(p)) > 1;
                count(remaining(p)) <= 3;
            };
        }
        have (3 - count(remaining(p))) + 1 == 3 - (count(remaining(p)) - 1) by {
            close() using {
                count(remaining(p)) > 1;
                count(remaining(p)) <= 3;
            };
        }
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
fail: Requires to_integer(p->value) == (3 - to_integer(count(remaining(p))))
```
