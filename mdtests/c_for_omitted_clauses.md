# C `for` loops with omitted initializer and step

The C0 `for` lowering permits an omitted initializer and/or step when the
condition is present. The omitted pieces lower to `skip`; unconditional loops
remain unsupported until `break` is modeled.

```c filename=for_omitted_clauses.c
int32 for_omitted_clauses() {
    int32 i = 0;
    for (; i < 3;) {
        i++;
    }
    return i;
}
```

```click
verifying "for_omitted_clauses.c";

int32 for_omitted_clauses() {
    ensures result == 3 by auto;
}
```

```expect
pass
```
