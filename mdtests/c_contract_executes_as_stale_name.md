# The target contract's own parameter spelling is not in scope

The conclusion introduces `k`, so the target's declared name `cell` names
nothing inside the proof block. The implicit lexical rule is gone.

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
    ensures Progress(callback) as { cell: k } by {
        step(Exact, { cell: cell });
        have cell.revision == old(cell.revision) + 1 by close();
        close();
    }
}
```

```expect
fail: unknown resource instance `cell`
```
