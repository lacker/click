# Viewability preservation refuses a call that may retire the range

The callee contract consumes an allocation and returns an allocation without
promising continuity. Its projected footprint is separate from the second
cell, but the call may retire the allocation containing that cell.

```c filename=probe.c
int32* replace(int32* p) { return p; }
int32* probe(int32* p) { return replace(p); }
```

```click
verifying "probe.c";
int32* replace(int32* p) {
    consumes allocation(p, 8);
    consumes p[0..1];
    produces allocation(result, 8);
    produces result[0..1];
}
int32* probe(int32* p) {
    consumes allocation(p, 8);
    consumes p[0..1];
    requires viewable(p[1..2]);
    produces allocation(result, 8);
    produces result[0..1];
} by {
    have separate(memory(p[0..1]), memory(p[1..2])) by { close(); }
    step();
    have separate(statement(0).call(0).footprint, memory(p[1..2])) by {
        close();
    }
    have viewable(p[1..2]) by {
        preserve(memory(p[1..2]), statement(0).call(0));
    }
    step_until(function.exit);
}
```

```expect
fail: preserve viewability requires a complete automatic-storage-only footprint
```
