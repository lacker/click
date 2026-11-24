# A call result is spelled by its call, after every local loses it

`make()` returns an allocation whose first element is 7. The caller stores it
in `h->p` and frees it through `h->p`. Right after the call the result lives
only in a frontend temporary, so the facts the call produced, such as
`owns allocation(r, 8)` and `r[0] == 7`, mention a value no Surface name
lowers to. `h->p` read after the store is a different term, equal to the
result only by the store's equation.

The call's result is named where it is introduced: a region has `entry` and
`exit` points and, for a call, a `result`, so `statement(0).call(make, 0).result`
is `make`'s result. The written fact lowers to the very fact the call produced,
so `close()` closes it.

```c filename=call_result.c
struct holder { int32* p; };
int32* make(void);
void f(struct holder* h) {
    h->p = make();
    free(h->p);
}
```

```click
extern int32* make() {
    produces allocation(result, 8);
    produces result[0..2];
    ensures result[0] == 7;
}
verifying "call_result.c";
void f(struct holder* h) {
    owns h->p;
} by {
    step();
    have statement(0).call(make, 0).result[0] == 7 by {
        close();
    }
    step_until(function.exit);
}
```

```expect
pass
```
