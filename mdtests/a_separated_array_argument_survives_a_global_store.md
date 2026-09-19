# a stated separation carries an array argument across a global store

The companion of `global_may_alias_an_array_argument.md`. The same body
verifies once the contract states the separation the block names do not
supply, and the read of `a[0]` is then framed across the store to `g[0]`.

```c filename=a_separated_array_argument_survives_a_global_store.c
int32 g[4];

void f(int32 a[], int32 n) {
    g[0] = 1;
}
```

```click
verifying "a_separated_array_argument_survives_a_global_store.c";

void f(int32 a[], int32 n) {
    requires 0 < n;
    requires loadable(a[0..n]);
    requires a[0] == 5;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures a[0] == 5;
    ensures g[0] == 1;
} by { execute(); simp(); }
```

```expect
pass
```
