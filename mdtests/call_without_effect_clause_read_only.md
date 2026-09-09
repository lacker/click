# Read-only contracts may omit an effect clause

An omitted function-level effect clause is an empty footprint, so a function
that only reads existing memory remains valid without spelling `immutable`.

```c filename=call_without_effect_clause_read_only.c
int32 value = 7;

int32 read_value() {
    return value;
}
```

```click
verifying "call_without_effect_clause_read_only.c";

int32 read_value() {
    requires value == 7;
    ensures result == 7;
}
```

```expect
pass
```
