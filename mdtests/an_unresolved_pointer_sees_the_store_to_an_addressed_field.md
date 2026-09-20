# an unresolved pointer sees the store to an addressed struct field

The companion of `an_unresolved_pointer_sees_the_store_to_a_local_array.md`.
`&s.first` forms an address of part of `s` without naming `s` under an `&` of
its own shape, and the store `s.first = 1` is recorded against `s`, so a rule
that asked only about `&s` would frame the read away from the store that
writes it.

The syntactic pass refuses every name mentioned anywhere below an
address-forming node, whatever the shape below it, and refuses an aggregate
name outright. Both answers say the same thing here, and the claim is false:
`q` is `&s.first`.

```c filename=an_unresolved_pointer_sees_the_store_to_an_addressed_field.c
struct pair { int32 first; int32 second; };

int32* echo(int32* p) { return p; }

void v(void) {
    struct pair s;
    int32* q;
    s.first = 5;
    q = echo(&s.first);
    s.first = 1;
}
```

```click
verifying "an_unresolved_pointer_sees_the_store_to_an_addressed_field.c";

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
fail: the store to `s` may have written it, and nothing tells that address apart from this read.
```
