# A named contract cannot take one instance for two proof parameters

`Pair` declares two `Counter` proof parameters. Applying it as `Pair(c, c)` is
refused at the step: an exclusive instance supplies at most one parameter, the
same rule a direct call map obeys
(`c_call_binder_transport_rejects_shared_instance.md`), and the kernel's shared
binder constructor refuses it again for a transport the surface did not see.

```c filename=c_named_contract_rejects_shared_instance.c
int32 invoke(int32 (*callback)()) { return callback(); }
```

```click
resource Counter() { field revision: int32; }

contract Pair(first: Counter(), second: Counter()) for int32() {
    owns first;
    owns second;
    ensures first.revision == old(first.revision);
    ensures second.revision == old(second.revision);
    ensures result == 0;
}

verifying "c_named_contract_rejects_shared_instance.c";

int32 invoke(int32 (*callback)()) {
    requires Pair(callback);
    owns c: Counter();
    ensures c.revision == old(c.revision);
    ensures result == 0;
} by {
    step(Pair(c, c));
    execute();
    simp();
}
```

```expect
fail: an exclusive instance cannot supply two contract proof parameters
```
