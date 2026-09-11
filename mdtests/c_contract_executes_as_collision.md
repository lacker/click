# An introduced instance name cannot shadow a call parameter

The `executes` clause already introduces the call argument `amount`, so the
conclusion cannot introduce a resource instance under the same name.

```click
resource Counter() { field revision: int32; field tag: int32; }
contract Exact(cell: Counter()) for int32(int32 amount) {
    owns cell;
    requires amount == 1;
    requires cell.revision < 2147483647;
    ensures cell.revision == old(cell.revision) + 1;
    ensures result == 0;
}
contract Progress(cell: Counter()) for int32(int32 amount) {
    owns cell;
    requires amount == 1;
    requires cell.revision < 2147483647;
    ensures cell.revision > old(cell.revision);
    ensures result == 0;
}
theorem lift(callback: int32 (*)(int32)) executes callback(int32 amount) {
    requires Exact(callback);
    ensures Progress(callback) as { cell: amount } by {
        step(Exact(amount));
        simp();
    }
}
```

```expect
fail: conflicts with an execution proof binding
```
