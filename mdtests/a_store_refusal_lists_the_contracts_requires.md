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

The note naming the uncovered end used to appear only when the held and needed
ranges shared a start; `owns b[0..n]` against `b[1..2]` now says the held range
covers it only when `2 <= n`.

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
fail: missing resource fact `owns b[1]`
  note: held `owns b[0..n]` covers `b[1]` only when `2 <= n`
  C operation: *(b + 1) = 1
  C statement at a_store_refusal_lists_the_contracts_requires.c:2:5: `b[1] = 1;`
proof context:
  pure facts: [0 <= n, 1 <= n, n <= 1073741823, n <= 1073741823 (unsigned), viewable(memory=snapshot#1, base=a, bytes:uint32=(n*4)), viewable(memory=snapshot#1, base=b, bytes:uint32=(n*4)), memory(b[Int32:0..n], stride=4) separate memory(a[Int32:0..n], stride=4), validated-composition { views memory(a[Int32:0..n], stride=4); owns memory(b[Int32:0..n], stride=4) x 1; support details omitted }]

  label definitions (recorded constructions, not additional facts):
    snapshot#1 = initial empty memory
  resource facts: [views a[0..n], owns b[0..n]]
```
