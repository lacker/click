# An `as` map cannot name a parameter the target does not declare

`Progress` declares `cell`, not `counter`, so the map keys nothing.

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
    ensures Progress(callback) as { counter: k } by {
        step(Exact(k));
        have k.revision == old(k.revision) + 1 by { assumption(); }
        apply(int32_increment_strictly_increases(old(k.revision), 2147483647));
        simp();
    }
}
```

```expect
fail: does not declare a proof parameter `counter`
```
