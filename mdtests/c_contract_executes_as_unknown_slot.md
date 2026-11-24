# An `as` map cannot name a parameter the target does not declare

`Progress` declares `cell`, not `counter`, so the map keys nothing.

```click
resource Counter() { field revision: int32; field tag: int32; }
contract int32 Exact() {
    owns cell: Counter();
    requires cell.revision < 2147483647;
    ensures cell.revision == old(cell.revision) + 1;
    ensures result == 0;
}
contract int32 Progress() {
    owns cell: Counter();
    requires cell.revision < 2147483647;
    ensures cell.revision > old(cell.revision);
    ensures result == 0;
}
theorem lift(callback: int32 (*)()) executes callback() {
    requires Exact(callback);
    ensures Progress(callback) as { counter: k } by {
        step(Exact, { cell: k });
        have k.revision == old(k.revision) + 1 by close();
        close();
    }
}
```

```expect
fail: does not declare a proof parameter `counter`
```
