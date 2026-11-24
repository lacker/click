# Open resource fields and witnesses denote their captured values

Writes change memory independently of the captured model. An explicit
fold can install a new field value. A scoped opening can read a witness
without another binding.

```c filename=open_members.c
void overwrite(int32 *p) { *p = 9; }
void read_witness(int32 *p) {}
```

```click
verifying "open_members.c";

resource tagged(p: int32*) {
    field tag: int32;
    owns *p;
}

resource witnessed(p: int32*) {
    field tag: int32;
    let base: int32* where base == p;
}

void overwrite(int32* p) {
    owns r: tagged(p);
    requires r.tag == 3;
    ensures r.tag == 4;
} by {
    unfold(r);
    step();
    have r.tag == 3 by close();
    let r = fold(tagged(p), { tag: 4 });
    have r.tag == 4 by close();
}

void read_witness(int32* p) {
    owns r: witnessed(p);
} by {
    with(r) {
        have r.base == p by close();
    }
}
```

```expect
pass
```
