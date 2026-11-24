# C-valued pure calls in owned child arguments

The model selects the child's address without reading the parent's C links.
The same checked argument is used when opening and rebuilding the resource.

```c filename=resource_child_pure_arguments.c
int32 read_child(int32* p) { return *p; }
```

```click
verifying "resource_child_pure_arguments.c";
spec enum Address { At(int32*) }
function model_pointer(model: Address) -> int32* {
    match model { Address::At(p) => p, }
}
resource cell(p: int32*) {
    field value: int32;
    owns p[0..1];
    fact p[0] == value;
}
resource holder() {
    field model: Address;
    field value: int32;
    owns child: cell(model_pointer(model));
    fact child.value == value;
}
int32 read_child(int32* p) {
    owns root: holder();
    requires root.model == Address::At(p);
    ensures result == old(root.value);
    ensures root.model == old(root.model);
    ensures root.value == old(root.value);
} by {
    have model_pointer(root.model) == p by {
        rewrite(root.model, Address::At(p));
        unfold(model_pointer(Address::At(p))); close();
    }
    let { child: child } = unfold(root);
    unfold(child);
    step_until(function.exit);
    let child = fold(cell(p), { value: old(root.value) });
    let root = fold(holder(), { model: old(root.model), value: old(root.value), child: child });
    close();
}
```

```expect
pass
```
