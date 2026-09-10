# A `mutable` contract clause is a parse error

Effect clauses were replaced by ownership. `mutable` no longer parses, and the
diagnostic names the replacement spelling.

```c filename=effect_clause_mutable_removed.c
int32 effect_clause_mutable_removed(int32* cell) {
    cell[0] = 1;
    return 0;
}
```

```click
verifying "effect_clause_mutable_removed.c";

int32 effect_clause_mutable_removed(int32* cell) {
    owns cell[0..1];
    mutable cell[0..1];
    ensures result == 0;
} by auto;
```

```expect
fail: effect clauses were removed; declare ownership with `owns` and `views`
```
