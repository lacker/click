# Pointer-valued existential witnesses

Pointer witnesses are complete symbolic pointers, not integer stand-ins. The
chosen pointer can be compared without making any claim that it is valid to
dereference or perform pointer arithmetic on it.

```c filename=pointer_existential_witness.c
int32 pointer_existential_witness(int32* p) {
    return 0;
}
```

```click
verifying "pointer_existential_witness.c";

int32 pointer_existential_witness(int32* p) {
    requires has_pointer: exists (q: int32*) { q == p };
    ensures preserves_pointer: exists (r: int32*) { r == p } by {
        execute();
        choose(q from requirement has_pointer);
        witness(r = q);
        simp();
    }
}
```

```expect
pass
```
