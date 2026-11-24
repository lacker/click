# A post-return fold in an open scope cannot invent the cell value

The write and return execute while the borrowed resource is open. Folding the
produced cell belongs to that returned path, before the scope closes, and must
use its updated value rather than the pre-execution frontier.

```c filename=resource_instance_fold_after_return_in_open.c
int f(int *p, int *q) { *q = 7; return 0; }
```

```click
verifying "resource_instance_fold_after_return_in_open.c";
resource borrowed(p: int32*) { owns p[0..1]; }
resource cell(p: int32*) {
    field value: int32;
    owns p[0..1];
    fact *p == value;
}
int32 f(int32* p, int32* q) {
    views borrowed(p);
    consumes input: cell(q);
    produces output: cell(q);
    ensures output.value == 7;
    ensures result == 0;
} by {
    unfold(input);
    with(borrowed(p)) {
        step_until(function.exit);
        let output = fold(cell(q), { value: 8 });
        close();
    }
}
```

```expect
fail: unproved obligation: `*q == (8 as int32)`
```
