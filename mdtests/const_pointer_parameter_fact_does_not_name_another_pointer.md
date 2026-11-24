# A fact about one `const` pointer parameter does not name another

The proof of
[`const_pointer_parameter_fact_survives_a_step.md`](const_pointer_parameter_fact_survives_a_step.md)
with a second `const` parameter `q`. The instance at `p` publishes
`same(p, p) == 1`. Leaving constness out of a pointer's identity leaves the
address in it, so that fact is not a fact about `q`, and `known` does
not find `same(q, q) == 1`.

The logical pointer annotations below use `void*` for address identities;
object access remains governed by the unchanged C types and resource ownership.

```c filename=const_parameter_other.c
struct node { int32 shade; };

int32 peek(const struct node* p, const struct node* q) {
    int32 seen = 0;
    return 0;
}
```

```click checked-only
verifying "const_parameter_other.c";

function same(a: void*, b: void*) -> int32 {
    if a == b { 1 } else { 0 }
}

resource here(p: struct node*) {
    field tag: int;
    owns p->shade;
    fact same(p, p) == 1;
}

int32 peek(const struct node* p, const struct node* q) {
    owns x: here(p);
    ensures result == 0;
} by {
    unfold(x);
    step();
    have same(q, q) == 1 by close();
    let x = fold(here(p), { tag: 0 });
    step();
    step();
    close();
}
```

```expect
fail: `known` requires the current goal as an available semantic fact
```
