# a returned pointer into a caller local still sees the store to that local

The attack on the pointer-equality hop. `echo` returns its argument, so in `v4`
the returned `q` *is* `&x`, and `x = 1` changes what `q[0]` reads. Resolving `q`
through `ensures result == p` is what lets the earlier read be proved at all —
and it is also what must make this later read fail, because the address it
resolves to is the very address the store wrote.

The hop is substitution of equals, not a separation claim: it moves the
question to `x`, and `x` is not proven distinct from itself. A rule that
separated a local from a pointer a call returned, rather than resolving it,
would admit this.

```c filename=returned_pointer_to_a_caller_local_may_alias_it.c
int32* echo(int32* p) { return p; }

void v4(void) {
    int32 x;
    int32* q;
    x = 5;
    q = echo(&x);
    x = 1;
}
```

```click
verifying "returned_pointer_to_a_caller_local_may_alias_it.c";

int32* echo(int32* p) {
    views p[0..1];
    requires p[0] == 5;
    ensures viewable(result[0..1]);
    ensures result[0] == 5;
    ensures result == p;
} by { execute(); simp(); }

void v4() {
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
fail: the store to `x` may have written it, and nothing tells that address apart from this read.
```
