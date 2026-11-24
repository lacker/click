# Implicit void-pointer helper arguments retain a member's selected view

Both an opaque call and its unfolded body use the same full pointer value.
The constructor's expected void-pointer type also retags without widening.
An explicit C-style cast remains a separate operation.

```c filename=case.c
struct pair { int first; int second; };
void keep(struct pair* p) {}
```

```click
verifying "case.c";
spec enum Link { At(void*), }
function identity(p: void*) -> void* { p }
function link(p: void*) -> Link { Link::At(p) }
void keep(struct pair* p) {
    owns p->first;
    ensures identity(0) == 0;
    ensures link(0) == Link::At(0);
    ensures identity(&p->first) == &p->first;
    ensures link(&p->first) == Link::At(&p->first);
} by {
    step_until(function.exit);
    unfold(identity(0));
    unfold(link(0));
    unfold(identity(&p->first));
    unfold(link(&p->first));
    close();
}
```

```expect
pass
```
