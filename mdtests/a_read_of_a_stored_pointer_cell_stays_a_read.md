# A read of a stored pointer cell stays a read

The pointer counterpart of `a_read_of_a_stored_cell_stays_a_read.md`. After
`a[i] = q`, the Click expression `a[i]` lowers to the read of that cell at the
store's version, not to the stored pointer `q`
(`docs/internals/raise-lower-principle.md`). The read-over-write authority relates the
read to the pointer the store wrote, so `a[i] == q` holds by evaluation, and a
rewrite that moves the read to an equal index keeps it a read: with `i == j`,
`rewrite(j, i)` turns the postcondition `a[j] == q` into `a[i] == q`, which
closes. Had `a[i]` lowered to `q`, the rewritten goal would no longer mention
`a`.

```c filename=set_pointer.c
void set_pointer(int32** a, int32* q, int32 i, int32 j) { a[i] = q; }
```

```click
verifying "set_pointer.c";
void set_pointer(int32** a, int32* q, int32 i, int32 j) {
    requires 0 <= i and i < 4;
    requires i == j;
    owns a[0..4];
    ensures a[j] == q;
} by {
    step_until(function.exit);
    have a[i] == q by known();
    known();
    rewrite(j, i);
}
```

```expect
pass
```
