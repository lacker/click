# Explicit opaque resource arguments cross a callback call

The selected instance keeps its identity, with fresh post-call fields related
to its entry fields only by explicit guarantees. The second instance is framed.
Neither instance provides access to C memory.

```c filename=invoke.c
int32 invoke(int32 (*callback)()) { return callback(); }
```

```click
verifying "invoke.c";

spec enum Mark { Clear, Set }
resource marker() { field model: Mark; field revision: int32; }

contract Touch(cell: marker()) for int32() {
    owns cell;
    ensures cell.model == old(cell.model);
    ensures cell.revision == 1;
    ensures result == 0;
}

int32 invoke(int32 (*callback)()) {
    requires Touch(callback);
    owns first: marker();
    owns second: marker();
    ensures first.model == old(first.model);
    ensures first.revision == 1;
    ensures second.model == old(second.model);
    ensures second.revision == old(second.revision);
    ensures result == 0;
} by {
    step(Touch(first));
    execute();
    simp();
}
```

```expect
pass
```
