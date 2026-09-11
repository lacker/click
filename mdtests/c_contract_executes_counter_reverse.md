# Progress alone does not promise an exact increment

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
    requires Progress(callback);
    ensures Exact(callback) as { cell: k } by {
        step(Progress(k));
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
fail: unclosed goal
```

