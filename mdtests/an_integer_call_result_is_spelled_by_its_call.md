# An integer call result is spelled by its call

`get()`'s result is stored in `h->x` and then overwritten, so only the
frontend's temporary held it. A proof states facts about it as
`statement(0).call(get, 0).result`, and a refusal names it the same way rather
than by the temporary.

```c filename=integer_call_result.c
struct holder { int32 x; };
int32 get(void);
void f(struct holder* h) {
    h->x = get();
    h->x = 0;
}
```

```click
extern int32 get() {
    ensures 0 <= result;
    ensures result < 100;
}
verifying "integer_call_result.c";
void f(struct holder* h) {
    owns h->x;
    ensures false;
} by {
    step();
    step();
    step();
    have statement(0).call(get, 0).result < 100 by {
        close();
    }
    have statement(0).call(get, 0).result == 5;
}
```

```expect
fail: goal: statement(0).call(get, 0).result == 5
```
