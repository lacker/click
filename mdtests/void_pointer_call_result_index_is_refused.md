# A `void *` call result is not indexed

`statement(0).call(get, 0).result` names `get`'s `void *` result, which has
no element type to step by, so `result[0]` is refused as `q[0]` is for a
`void *` `q` (`void_pointer_spec_index_is_refused.md`). Click once read it as
an `int32`. A cast states the type:
`(statement(0).call(get, 0).result as (int32 *))[0]`.

```c filename=void_pointer_call_result_index_is_refused.c
struct holder { void *p; };
void *get(void);
void keep(struct holder *h) {
    h->p = get();
}
```

```click
extern void* get() {
    produces (result as (int32 *))[0..1];
    ensures (result as (int32 *))[0] == 5;
}
verifying "void_pointer_call_result_index_is_refused.c";
void keep(struct holder* h) {
    owns h->p;
} by {
    step();
    have statement(0).call(get, 0).result[0] == 5 by {
        close();
    }
    step_until(function.exit);
}
```

```expect
fail: a `void *` has no pointee type; cast it to a typed pointer or use `load<T>`
```
