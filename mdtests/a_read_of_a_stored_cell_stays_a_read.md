# A read of a stored cell stays a read

After `a[i] = 5`, the Click expression `a[i]` lowers to the read of that cell
at the store's version, not to the stored value `5`: every read lowers to its
version name (`docs/internals/raise-lower-principle.md`). The read-over-write authority
relates the read to the value the store wrote, so `a[i] == 5` is a goal that
holds by evaluation and `normalize` closes it, while the goal itself still
names the read. A rewrite that moves a read to an equal address keeps it a
read: with `i == j`, `rewrite(j, i)` turns the postcondition `a[j] == 5`
into `a[i] == 5`, which holds by evaluation, so the rewrite closes it. If
`a[i]` lowered to `5`, the rewritten goal would be `true`, no longer about
`a` at all.

```c filename=set.c
void set(int32* a, int32 i, int32 j) { a[i] = 5; }
```

```click
verifying "set.c";
void set(int32* a, int32 i, int32 j) {
    requires 0 <= i and i < 4;
    requires i == j;
    owns a[0..4];
    ensures a[j] == 5;
} by {
    step_until(function.exit);
    have a[i] == 5 by normalize();
    known();
    rewrite(j, i);
}
```

```expect
pass
```
