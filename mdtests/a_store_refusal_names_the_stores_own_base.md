# a store refusal names the range against the store's own base

`n` may be `0`, so the store to `b[0]` really is unjustified. The refusal used
to spell the resource it needed as

```text
missing resource fact `owns a[(v100001 - v100000)..((v100001 - v100000) + 1)]`
```

the same bytes expressed as an offset from the *other* parameter's base, with
two kernel variables in it. Every external pointer parameter shares one block,
so any of them can name the range symbolically; the refusal now spells it
against the parameter it sits at a constant offset from, `b`. It also says what
the verdict compared: the held `owns b[0..n]` covers `b[0..1]` only when
`1 <= n`.

```c filename=a_store_refusal_names_the_stores_own_base.c
void walk(int32 *a, int32 *b, int32 n) {
    b[0] = 1;
}
```

```click
verifying "a_store_refusal_names_the_stores_own_base.c";

void walk(int32 *a, int32 *b, int32 n) {
    views a[0..n];
    owns b[0..n];
    requires 0 <= n;
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact `owns b[0..1]`
  note: held `owns b[0..n]` covers `b[0..1]` only when `1 <= n`
```
