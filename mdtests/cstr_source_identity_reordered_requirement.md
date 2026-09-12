# Dynamic C-string retry keeps the exact caller requirement identity

The relevant predicate requirement is deliberately not the first entry
clause.  Unrelated arithmetic, loadability, and resource facts also ensure
that its source ordinal is not its final lowered fact position.

```c filename=cstr_source_identity_reordered_requirement.c
int32 read_terminator(uint8 haystack[], int32 known_len) {
    int32 length;
    length = strlen(haystack);
    return length;
}
```

```click
verifying "cstr_source_identity_reordered_requirement.c";

int32 read_terminator(uint8 haystack[], int32 known_len) {
    requires nonnegative: 0 <= known_len;
    requires successor: defined(known_len + 1);
    requires unrelated: loadable(haystack[0..known_len + 1]);
    requires input: cstr_readable(haystack);
    views haystack[0..known_len + 1];
    ensures result >= 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
