# a struct-pointer local is a memory base in its function's proof

A contract's parameters carry their struct names from the signature, so
`root->value` in a `have` has a layout. An automatic local declared in the C
body had none: `syntax::C0Function` recorded globals, static locals and
aggregates but not the body's own declarations, so `p->value` lowered to no
path at all even when `p` provably aliased `root`.

The C parser now records the struct name of every automatic local of
struct-pointer type under its C spelling, and the sidecar parser adds those to
the function's struct parameters. A parameter of the same spelling wins,
because a contract is written against the signature.

A local a proof names before the execution has run its assignment is refused by
name instead of by a path count; that is
`mdtests/have_names_a_local_before_its_assignment.md`.

```c filename=struct_pointer_local_has_a_layout.c
struct cell {
    int32 value;
    struct cell* next;
};

int32 alias_read(struct cell *root) {
    struct cell *p;

    p = root;
    return p->value;
}
```

```click
verifying "struct_pointer_local_has_a_layout.c";

int32 alias_read(struct cell* root) {
    owns root->value;
    requires root != 0;
    ensures result == old(root->value);
} by {
    step();
    step();
    have p->value == root->value by { simp(); }
    step();
    simp();
}
```

```expect
pass
```
