# a call through a function pointer cannot lend and transfer one range

`a_caller_cannot_lend_and_transfer_one_range.md` through an interface. The
callee is reached as a `contract` carried by a function pointer, so nothing
about the direct-call path can be what refuses it; the same funnel
(`prepare_function_resource_transfer` → `prepare_contract_resource_transfer`)
and the same fail-closed planner decide both.

```c filename=a_function_pointer_caller_cannot_lend_and_transfer_one_range.c
int32 g[4];

void split(int32 *a, int32 *b) {
    a[0] = 1;
}

void caller(void (*f)(int32 *, int32 *)) {
    f(g, g);
}
```

```click
verifying "a_function_pointer_caller_cannot_lend_and_transfer_one_range.c";

contract void Split(int32* a, int32* b) {
    owns a[0..1];
    views b[0..1];
    ensures a[0] == 1;
}

void split(int32* a, int32* b) {
    owns a[0..1];
    views b[0..1];
    ensures a[0] == 1;
} by { execute(); simp(); }

void caller(void (*f)(int32*, int32*)) {
    requires Split(f);
    owns g[0..4];
    ensures g[0] == 1;
} by { execute(); simp(); }
```

```expect
fail: `caller.contract` tactic 0: `step()` produced runtime error: stable-view a required resource overlaps a live borrowed footprint refused during planning; selected resource `owns global:g@0[0..1]`
```
