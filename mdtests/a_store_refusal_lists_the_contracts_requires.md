# a store refusal lists the contract's `requires` in its proof context

`1 <= n` does not justify a store to `b[1]`, which needs `2 <= n`, so the step
is refused. Its proof context used to read

```text
proof context:
  pure facts: []
```

although the step checked the store against `requires 1 <= n` and the range
guards the contract's clauses carry. A step inside a proof hands the kernel
that whole context and passes its fact list only as the statement-local delta,
and the refusal listed the delta alone. It now lists the context the step was
checked against, with each true condition spelled as the comparison it states.

```c filename=a_store_refusal_lists_the_contracts_requires.c
void walk(int32 *a, int32 *b, int32 n) {
    b[1] = 1;
}
```

```click
verifying "a_store_refusal_lists_the_contracts_requires.c";

void walk(int32 *a, int32 *b, int32 n) {
    views a[0..n];
    owns b[0..n];
    requires 1 <= n;
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact `owns b[1..2]`
  C operation: *(b + 1) = 1
proof context:
  pure facts: [0 <= n, 1 <= n, n <= 1073741823, n <= 1073741823 (unsigned), viewable(base=a, bytes=(n * 4)), viewable(base=b, bytes=(n * 4)), separate(memory(b[0..n]), memory(a[0..n]))]
  resource facts: [views a[0..n], owns b[0..n]]
```
