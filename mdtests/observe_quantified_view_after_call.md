# Observing a quantified view after a disjoint call

```c filename=observe_quantified_view_after_call.c
void mark(int32* data, int32* marks, int32 n) {
    marks[0] = 1;
}

void caller(int32* data, int32* marks, int32 n) {
    mark(data, marks, n);
}
```

```click
verifying "observe_quantified_view_after_call.c";

predicate positive(n: int32) {
    0 < n
}

resource bounded(data: int32*, n: int32) {
    views data[0..n];
    fact 0 < n;
    fact positive(n);
    fact forall (k: int32) { 0 <= k and k < n implies 0 <= data[k] };
}

void mark(int32* data, int32* marks, int32 n) {
    views bounded(data, n);
    owns marks[0..n];
    requires separate(memory(data[0..n]), memory(marks[0..n]));
} by {
    execute();
    simp();
}

void caller(int32* data, int32* marks, int32 n) {
    views bounded(data, n);
    owns marks[0..n];
    requires separate(memory(data[0..n]), memory(marks[0..n]));
} by {
    step();
    observe(bounded(data, n));
    step();
    simp();
}
```

```expect
pass
```
