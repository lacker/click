# An introduced instance name cannot shadow the executed callback

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
theorem lift(cell: int32 (*)()) executes cell() {
    requires Exact(cell);
    ensures Progress(cell) as { cell: cell } by {
        step(Exact(cell));
        have cell.revision == old(cell.revision) + 1 by { assumption(); }
        apply(int32_increment_strictly_increases(old(cell.revision), 2147483647));
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
fail: conflicts with an execution proof binding
```

