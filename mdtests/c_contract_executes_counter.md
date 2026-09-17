# Refine an exact resource-field update to progress

The theorem selects the target contract's arbitrary counter instance. The
caller applies the resulting contract to one counter and frames a second.

```c filename=counter.c
int32 invoke(int32 (*callback)()) { return callback(); }
```

```click
resource Counter() { field revision: int32; field tag: int32; }
contract Exact(cell: Counter()) for int32() {
    owns cell;
    requires cell.revision < 2147483647;
    ensures cell.revision == old(cell.revision) + 1;
    ensures result == 0;
}
contract Progress(cell: Counter()) for int32() {
    owns cell;
    requires cell.revision < 2147483647;
    ensures cell.revision > old(cell.revision);
    ensures result == 0;
}
theorem lift(callback: int32 (*)()) executes callback() {
    requires Exact(callback);
    ensures Progress(callback) as { cell: k } by {
        step(Exact(k));
        have k.revision == old(k.revision) + 1 by { assumption(); }
        apply(int32_increment_strictly_increases(old(k.revision), 2147483647));
        simp();
    }
}
verifying "counter.c";
int32 invoke(int32 (*callback)()) {
    requires Exact(callback);
    owns first: Counter();
    owns second: Counter();
    requires first.revision < 2147483647;
    ensures first.revision > old(first.revision);
    ensures second.revision == old(second.revision);
    ensures second.tag == old(second.tag);
    ensures result == 0;
} by {
    apply(lift(callback));
    step(Progress(first));
    execute();
    simp();
}
```

```expect
pass
```
