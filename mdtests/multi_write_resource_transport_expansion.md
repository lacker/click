# Multiple statements preserve an abstract resource field

Each store has its own separation fact and preservation step. The two
equalities connect the resource field at the entrance to the first store
with its value after the second store.

```c filename=keep.c
void keep(unsigned char *p) { *p = 0; *p = 1; }
```

```click
verifying "keep.c";
abstract resource model() { field value: int32; }
void keep(uint8* p) {
    owns *p;
    owns m: model();
    requires separate(memory(*p), m);
} by {
    step();
    have separate(statement(0).footprint, m) by {
        close() using { separate(memory(*p), m); };
    }
    step();
    have separate(statement(1).footprint, m) by {
        close() using { separate(memory(*p), m); };
    }
    have at(statement(0).exit, m.value) == at(statement(0).entry, m.value) by {
        preserve(m, statement(0));
    }
    have m.value == at(statement(1).entry, m.value) by {
        preserve(m, statement(1));
    }
    have m.value == at(statement(0).entry, m.value) by { close(); }
    step();
}
```

```expect
pass
```
