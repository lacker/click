# a universal witness does not inherit a C variable's facts

`intro` on a universal replaces the bound variable by a free identity standing
for an arbitrary value. If that identity is one a C variable already has, then
every fact about the variable is a fact about the witness, and the universal
this proof would close is about the variable rather than about everything.

The freshener used to choose the witness by counting up from `Variable(0)` for
an identity no fact mentions, which is the C identity range, so the earlier
universal below — whose only effect is to reserve the binder identity both
`have`s lower into — was enough to send the second one there. `m == 5` is a
fact about the first parameter and must stay one: `forall (k) { ... k == 5 }`
is false for every `n` above one.

```c filename=universal_witness_does_not_inherit_facts.c
int32 walk(int32 m, int32 n) {
    return m;
}
```

```click
verifying "universal_witness_does_not_inherit_facts.c";

int32 walk(int32 m, int32 n) {
    requires 1 <= n;
    requires m == 5;
    ensures result == 5;
} by {
    have forall (j: int32) {
        0 <= j and j < n implies 0 <= j
    } by {
        intro();
        intro();
        extract(0 <= j);
        assumption();
    }
    have forall (k: int32) {
        0 <= k and k < n implies k == 5
    } by {
        intro();
        intro();
        assumption();
    }
    execute();
    simp();
}
```

```expect
fail: `assumption` requires the current goal as an available semantic fact
```
