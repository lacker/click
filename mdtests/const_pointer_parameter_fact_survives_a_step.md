# A fact about a `const` pointer parameter survives a C step

`peek` takes `const struct node* p`. Unfolding `x` publishes the body fact
`same(p, p) == 1`, and after a C step the proof still finds it by
`known`.

It used to be lost. Whether a pointer's pointee is `const` was part of the
pointer value's identity, so the fact built from the instance's argument and
the parameter read back after the step, with its declared `const`, were two
different terms for one pointer. Constness is now carried beside the value
and left out of its identity: it is a property of the access path, which the
write checks read, and two pointers that differ only in it designate the same
object. Writes through a `const` view are still refused
(`const_pointer_write_rejected.md`, `const_pointer_cast_write_rejected.md`),
and a fact about `p` says nothing about another pointer
([`const_pointer_parameter_fact_does_not_name_another_pointer.md`](const_pointer_parameter_fact_does_not_name_another_pointer.md)).

The logical pointer annotations below use `void*` for address identities;
object access remains governed by the unchanged C types and resource ownership.

```c filename=const_parameter_fact.c
struct node { int32 shade; };

int32 peek(const struct node* p) {
    int32 seen = 0;
    return 0;
}
```

```click
verifying "const_parameter_fact.c";

function same(a: void*, b: void*) -> int32 {
    if a == b { 1 } else { 0 }
}

resource here(p: struct node*) {
    field tag: int;
    owns p->shade;
    fact same(p, p) == 1;
}

int32 peek(const struct node* p) {
    owns x: here(p);
    ensures result == 0;
} by {
    unfold(x);
    step();
    have same(p, p) == 1 by close();
    let x = fold(here(p), { tag: 0 });
    step();
    step();
    close();
}
```

```expect
pass
```
