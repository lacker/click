# A named contract cannot be applied to an instance a previous call consumed

`Take` consumes its `Counter` proof parameter. The caller applies it to `c`
twice. At the second application `c` is no longer owned, and the kernel refuses
the proof argument with the same refusal a direct call map gets
(`c_call_binder_transport_rejects_consumed_instance.md`).

```c filename=c_named_contract_rejects_consumed_instance.c
int32 invoke(int32 (*callback)()) { callback(); return callback(); }
```

```click
resource Counter() { field revision: int32; }

contract Take(first: Counter()) for int32() {
    consumes first;
    ensures result == 0;
}

verifying "c_named_contract_rejects_consumed_instance.c";

int32 invoke(int32 (*callback)()) {
    requires Take(callback);
    consumes c: Counter();
    ensures result == 0;
} by {
    step(Take(c));
    step(Take(c));
    execute();
    simp();
}
```

```expect
fail: resource proof argument is not owned
```
