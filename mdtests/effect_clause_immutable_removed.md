# An `immutable` contract clause is a parse error

A contract that owns nothing already promises it writes nothing, so
`immutable` has no spelling of its own and the diagnostic points at ownership.

```c filename=effect_clause_immutable_removed.c
int32 effect_clause_immutable_removed(int32* cell) {
    return cell[0];
}
```

```click
verifying "effect_clause_immutable_removed.c";

int32 effect_clause_immutable_removed(int32* cell) {
    views cell[0..1];
    immutable;
    ensures result == cell[0];
} by auto;
```

```expect
fail: effect clauses were removed; declare ownership with `owns` and `views`
```
