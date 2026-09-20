# an unresolved pointer sees the store to an addressed parameter

A parameter is an automatic object like any other: it has storage, its address
can be taken, and a pointer that escaped through a call can come back
designating it. The pass that decides which automatic objects the program
never addresses therefore declares parameters alongside locals, and refuses
this one for the `&x` in its own body.

The claim is false: `q` is `&x`, and `x = 1` writes what `q` reads.

```c filename=an_unresolved_pointer_sees_the_store_to_an_addressed_parameter.c
int32* echo(int32* p) { return p; }

void v(int32 x) {
    int32* q;
    x = 5;
    q = echo(&x);
    x = 1;
}
```

```click
verifying "an_unresolved_pointer_sees_the_store_to_an_addressed_parameter.c";

int32* echo(int32* p) {
    views p[0..1];
    requires p[0] == 5;
    ensures viewable(result[0..1]);
    ensures result[0] == 5;
} by { execute(); simp(); }

void v(int32 x) {
    ensures 1 == 1;
} by {
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
fail: the store to `x` may have written it, and nothing tells that address apart from this read.
```
