# resource verbs support explicit composite proofs

This checks the canonical function-level resource surface. `owns` carries an
explicit unfold/execute/fold proof, `views` uses the composite core, and a
`consumes`/`produces` pair describes a resource-state transition.

```c filename=initialize_cell.c
int32 initialize_cell(int32 p[]) {
    p[0] = 0;
    return p[0];
}
```

```c filename=set_cell_one.c
int32 set_cell_one(int32 p[]) {
    p[0] = 1;
    return p[0];
}
```

```c filename=inspect_cell.c
int32 inspect_cell(int32 p[]) {
    return p[0];
}
```

```click
resource initialized_cell(p: int32*) {
    owns p[0..1];
    fact p[0] >= 0;
}

verifying "initialize_cell.c";
verifying "set_cell_one.c";
verifying "inspect_cell.c";

int32 initialize_cell(int32 p[]) {
    consumes p[0..1];
    produces initialized_cell(p) by {
        execute();
        fold(initialized_cell(p));
    }
}

int32 set_cell_one(int32 p[]) {
    owns initialized_cell(p) by {
        unfold(initialized_cell(p));
        execute();
        fold(initialized_cell(p));
    }
}

int32 inspect_cell(int32 p[]) {
    views initialized_cell(p);
    ensures result >= 0 by auto;
}
```

```expect
pass
```
