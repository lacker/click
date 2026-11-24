# Model-derived child memory belongs to the call's write footprint

```c filename=resource_child_pure_arguments_write_footprint.c
void overwrite(int32* p) { *p = 1; }
void caller(int32* p) { *p = 0; overwrite(p); }
```
```click
verifying "resource_child_pure_arguments_write_footprint.c";
spec enum Address { At(int32*) }
function model_pointer(model: Address) -> int32* { match model { Address::At(p) => p, } }
resource cell(p: int32*) { field tag: int32; owns p[0..1]; }
resource holder(p: int32*) {
    field model: Address;
    field tag: int32;
    owns child: cell(model_pointer(model));
    fact model == Address::At(p);
    fact child.tag == tag;
}
void overwrite(int32* p) {
    owns root: holder(p);
    ensures root.model == old(root.model);
    ensures root.tag == old(root.tag);
} by {
    let { child: c } = unfold(root);
    have model_pointer(old(root.model)) == p by { rewrite(old(root.model), Address::At(p)); unfold(model_pointer(Address::At(p))); normalize(); }
    unfold(c);
    step_until(function.exit);
    let c = fold(cell(p), { tag: old(root.tag) });
    let root = fold(holder(p), { model: old(root.model), tag: old(root.tag), child: c });
    close();
}
void caller(int32* p) {
    owns root: holder(p);
    ensures p[0] == 0;
} by {
    let { child: c } = unfold(root);
    have model_pointer(old(root.model)) == p by { rewrite(old(root.model), Address::At(p)); unfold(model_pointer(Address::At(p))); normalize(); }
    unfold(c);
    step();
    mark before_call;
    have p[0] == 0 by close();
    let c = fold(cell(p), { tag: old(root.tag) });
    let root = fold(holder(p), { model: old(root.model), tag: old(root.tag), child: c });
    step();
    let { child: c } = unfold(root);
    unfold(c);
    have p[0] == at(before_call, p[0]) by {
        close();
    }
}
```
```expect
fail: `have` failed for `p[0] == at(before_call, p[0])`
```
