# an unresolved pointer sees the store to a local array

An automatic object whose address the program never forms is separate from
every pointer value, and that is what frames the ordinary `p = f(); … p[0]`.
An array is the first of the two ways C hands out such an address without an
`&` anywhere: the name `a` in `echo(a)` *is* `&a[0]`.

So the registry behind that rule refuses a name that is declared with an array,
struct or union type anywhere in the program, rather than asking whether that
particular use looked like an address. Here `q` really is `&a[0]`, `a[0] = 1`
really does write what `q` reads, and the claim is false.

```c filename=an_unresolved_pointer_sees_the_store_to_a_local_array.c
int32* echo(int32* p) { return p; }

void v(void) {
    int32 a[4];
    int32* q;
    a[0] = 5;
    q = echo(a);
    a[0] = 1;
}
```

```click
verifying "an_unresolved_pointer_sees_the_store_to_a_local_array.c";

int32* echo(int32* p) {
    views p[0..1];
    requires p[0] == 5;
    ensures viewable(result[0..1]);
    ensures result[0] == 5;
} by { execute(); simp(); }

void v() {
    ensures 1 == 1;
} by {
    step();
    step();
    step();
    step();
    step();
    have q[0] == 5 by { simp(); }
    execute();
    simp();
}
```

```expect
fail: the store to `a` may have written it, and nothing tells that address apart from this read.
```
